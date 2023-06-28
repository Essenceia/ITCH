/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

module tv_itch5 #(
	`ifdef DEBUG_ID
	parameter DEBUG_ID_W = 64,
	`endif
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = AXI_DATA_W / 8,
	parameter KEEP_LW    = $clog2(AXI_KEEP_W) + 1,
	
	// itch data
	parameter LEN = 8,

	// maximum length an itch message ( net order imbalance )
	parameter MSG_MAX_N = 50*LEN, 
	parameter MSG_MAX_W = $clog2(MSG_MAX_N+1), 

	// maxium number of payloads that need to be received for the longest itch message 
	parameter PL_MAX_N = 7, // $ceil(MSG_MAX_W / AXI_DATA_W)
	parameter PL_MAX_W = $clog2(PL_MAX_N)
)(
	input clk,
	input nreset,

	`ifdef DEBUG_ID
	// debug id associated with current message, used to track
	// messages through pipeline for debug
	input  [DEBUG_ID_W-1:0] debug_id_i,
	output [DEBUG_ID_W-1:0] debug_id_o,
	`endif 

	//message
	input                  valid_i,
	input                  start_i,
	input [KEEP_LW-1:0]    len_i,
	input [AXI_DATA_W-1:0] data_i
	
);
// itch interface
tv_itch5_if #(.LEN(LEN)) itch_o();
`ifdef EARLY
tv_itch5_early_if early_o();
`endif
// received byte counter
reg   [MSG_MAX_W-1:0]  data_cnt_q;
logic [MSG_MAX_W-1:0]  data_cnt_next;
logic [MSG_MAX_W-1:0]  data_cnt_add;
logic                  data_cnt_add_overflow;
logic                  data_cnt_en;
// itch message type
logic [LEN-1:0]        itch_msg_type;
logic                  itch_msg_sent;
`ifdef DEBUG_ID
reg   [DEBUG_ID_W-1:0] debug_id_q;
logic [DEBUG_ID_W-1:0] debug_id_next;
logic                  debug_id_en;
`endif

// count number of recieved bytes
assign { data_cnt_add_overflow, data_cnt_add } = data_cnt_q + { {MSG_MAX_W-KEEP_LW{1'b0}}, len_i};
// reset to 1 when new msg start, can't set to 0 as we are implicity using
// this counter as a valid signal  
assign data_cnt_next = start_i ? { {MSG_MAX_W-KEEP_LW{1'b0}}, len_i }  : 
					   itch_msg_sent ? {PL_MAX_W{1'b0}} : data_cnt_add; 

assign data_cnt_en = valid_i | itch_msg_sent;
always @(posedge clk) begin
	if ( ~nreset ) begin
		data_cnt_q <= 1'b0;
	end else if ( data_cnt_en ) begin
		data_cnt_q <= data_cnt_next;
	end
end
// convert length to mask
logic [AXI_KEEP_W-1:0]   data_mask;
len_to_mask #(.LEN_W(KEEP_LW), .LEN_MAX(AXI_KEEP_W) )
m_itch_len_to_mask(
	.len_i(len_i),
	.mask_o(data_mask)
);

// shift received bytes into the correct position
// data_shifted unused bits are writen to x
logic [2*AXI_KEEP_W-1:0] data_mask_shifted_arr[AXI_KEEP_W-1:0];
logic [2*AXI_DATA_W-1:0] data_shifted_arr[AXI_KEEP_W-1:0];
logic [2*AXI_KEEP_W-1:0] data_mask_shifted;
logic [2*AXI_DATA_W-1:0] data_shifted;

genvar i;
generate
	for(i=0; i<AXI_KEEP_W; i++)begin
		assign data_mask_shifted_arr[i] = { {AXI_KEEP_W-i{1'b0}} , data_mask, {i{1'b0}} };
		assign data_shifted_arr[i]      = { {AXI_DATA_W-i*LEN{1'bx}}, data_i, {i*LEN{1'bx}}};
	end
endgenerate
always_comb begin
	for(int j=0; j<AXI_KEEP_W; j++)begin
		if( len_i == j ) data_mask_shifted = data_mask_shifted_arr[j];
		if( len_i == j ) data_shifted      = data_shifted_arr[j];
	end
end

// write select bytes by groups of 8
// data storage
localparam LEN_W = $clog2(LEN);

reg   [MSG_MAX_N-1:0] data_q;
logic [MSG_MAX_N-1:0] data_next;
logic [PL_MAX_N-1:0]  data_en;
logic [PL_MAX_N-1:0]  data_start_en; 
logic [PL_MAX_N-1:0]  data_end_en; 
logic [MSG_MAX_W-1:0] data_cnt_lite;
logic [MSG_MAX_W-1:0] cnt_end;
logic                 cnt_end_offset;
logic                 data_overlap; // overlap on 8 byte data boundary

logic [PL_MAX_N*AXI_DATA_W-1:MSG_MAX_N] data_next_unused;

assign data_cnt_lite = start_i ? 'd0 : data_cnt_q;
assign { cnt_end_offset, cnt_end } = data_cnt_lite + { {MSG_MAX_W-KEEP_LW{1'b0}},len_i};
assign data_overlap = ~|data_cnt_lite[LEN_W-1:0]; 
generate
	for(i=0; i<PL_MAX_N; i++) begin
		// enable
		assign data_start_en[i] = ( data_cnt_lite[MSG_MAX_W-1:LEN_W] == i ); 
		assign data_end_en[i]   = ( cnt_end[MSG_MAX_W-1:LEN_W] == i );
		assign data_en[i] = ( data_start_en[i] | data_end_en[i] ) & valid_i;
 		// data next
		if ( i == PL_MAX_N -1 ) begin
			assign { data_next_unused , data_next[MSG_MAX_N-1:i*AXI_DATA_W] } =	data_overlap ?
				data_shifted[2*AXI_DATA_W-1:AXI_DATA_W] : data_shifted[AXI_DATA_W-1:0];
		end else begin
			assign data_next[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W] = data_overlap ?
				data_shifted[2*AXI_DATA_W-1:AXI_DATA_W] : data_shifted[AXI_DATA_W-1:0];
		end
		always @(posedge clk) begin
			if(data_en[i]) begin
				if ( i == PL_MAX_N-1 ) begin 
					data_q[MSG_MAX_N-1:i*AXI_DATA_W] <= data_next[MSG_MAX_N-1:i*AXI_DATA_W]; 
				end else begin
					data_q[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W] <= data_next[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W]; 
				end
			end
		end
	end
endgenerate


logic system_event_lite_v;
assign system_event_lite_v = (itch_msg_type == "S");
assign itch_o.system_event_v = system_event_lite_v & (data_cnt_q == 'd12);
assign itch_o.system_event_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.system_event_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.system_event_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.system_event_event_code = data_q[LEN*11+LEN*1-1:LEN*11];

logic stock_directory_lite_v;
assign stock_directory_lite_v = (itch_msg_type == "R");
assign itch_o.stock_directory_v = stock_directory_lite_v & (data_cnt_q == 'd39);
assign itch_o.stock_directory_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.stock_directory_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.stock_directory_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.stock_directory_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.stock_directory_market_category = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_o.stock_directory_financial_status_indicator = data_q[LEN*20+LEN*1-1:LEN*20];
assign itch_o.stock_directory_round_lot_size = data_q[LEN*21+LEN*4-1:LEN*21];
assign itch_o.stock_directory_round_lots_only = data_q[LEN*25+LEN*1-1:LEN*25];
assign itch_o.stock_directory_issue_classification = data_q[LEN*26+LEN*1-1:LEN*26];
assign itch_o.stock_directory_issue_sub_type = data_q[LEN*27+LEN*2-1:LEN*27];
assign itch_o.stock_directory_authenticity = data_q[LEN*29+LEN*1-1:LEN*29];
assign itch_o.stock_directory_short_sale_threshold_indicator = data_q[LEN*30+LEN*1-1:LEN*30];
assign itch_o.stock_directory_ipo_flag = data_q[LEN*31+LEN*1-1:LEN*31];
assign itch_o.stock_directory_luld_reference_price_tier = data_q[LEN*32+LEN*1-1:LEN*32];
assign itch_o.stock_directory_etp_flag = data_q[LEN*33+LEN*1-1:LEN*33];
assign itch_o.stock_directory_etp_leverage_factor = data_q[LEN*34+LEN*4-1:LEN*34];
assign itch_o.stock_directory_inverse_indicator = data_q[LEN*38+LEN*1-1:LEN*38];

logic stock_trading_action_lite_v;
assign stock_trading_action_lite_v = (itch_msg_type == "H");
assign itch_o.stock_trading_action_v = stock_trading_action_lite_v & (data_cnt_q == 'd25);
assign itch_o.stock_trading_action_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.stock_trading_action_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.stock_trading_action_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.stock_trading_action_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.stock_trading_action_trading_state = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_o.stock_trading_action_reserved = data_q[LEN*20+LEN*1-1:LEN*20];
assign itch_o.stock_trading_action_reason = data_q[LEN*21+LEN*4-1:LEN*21];

logic reg_sho_restriction_lite_v;
assign reg_sho_restriction_lite_v = (itch_msg_type == "Y");
assign itch_o.reg_sho_restriction_v = reg_sho_restriction_lite_v & (data_cnt_q == 'd20);
assign itch_o.reg_sho_restriction_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.reg_sho_restriction_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.reg_sho_restriction_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.reg_sho_restriction_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.reg_sho_restriction_reg_sho_action = data_q[LEN*19+LEN*1-1:LEN*19];

logic market_participant_position_lite_v;
assign market_participant_position_lite_v = (itch_msg_type == "L");
assign itch_o.market_participant_position_v = market_participant_position_lite_v & (data_cnt_q == 'd26);
assign itch_o.market_participant_position_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.market_participant_position_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.market_participant_position_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.market_participant_position_mpid = data_q[LEN*11+LEN*4-1:LEN*11];
assign itch_o.market_participant_position_stock = data_q[LEN*15+LEN*8-1:LEN*15];
assign itch_o.market_participant_position_primary_market_maker = data_q[LEN*23+LEN*1-1:LEN*23];
assign itch_o.market_participant_position_market_maker_mode = data_q[LEN*24+LEN*1-1:LEN*24];
assign itch_o.market_participant_position_market_participant_state = data_q[LEN*25+LEN*1-1:LEN*25];

logic mwcb_decline_level_lite_v;
assign mwcb_decline_level_lite_v = (itch_msg_type == "V");
assign itch_o.mwcb_decline_level_v = mwcb_decline_level_lite_v & (data_cnt_q == 'd35);
assign itch_o.mwcb_decline_level_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.mwcb_decline_level_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.mwcb_decline_level_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.mwcb_decline_level_level_1 = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.mwcb_decline_level_level_2 = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_o.mwcb_decline_level_level_3 = data_q[LEN*27+LEN*8-1:LEN*27];

logic mwcb_status_lite_v;
assign mwcb_status_lite_v = (itch_msg_type == "W");
assign itch_o.mwcb_status_v = mwcb_status_lite_v & (data_cnt_q == 'd12);
assign itch_o.mwcb_status_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.mwcb_status_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.mwcb_status_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.mwcb_status_breached_level = data_q[LEN*11+LEN*1-1:LEN*11];

logic ipo_quoting_period_update_lite_v;
assign ipo_quoting_period_update_lite_v = (itch_msg_type == "K");
assign itch_o.ipo_quoting_period_update_v = ipo_quoting_period_update_lite_v & (data_cnt_q == 'd28);
assign itch_o.ipo_quoting_period_update_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.ipo_quoting_period_update_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.ipo_quoting_period_update_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.ipo_quoting_period_update_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.ipo_quoting_period_update_ipo_quotation_release_time = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_o.ipo_quoting_period_update_ipo_quotation_release_qualifier = data_q[LEN*23+LEN*1-1:LEN*23];
assign itch_o.ipo_quoting_period_update_ipo_price = data_q[LEN*24+LEN*4-1:LEN*24];

logic luld_auction_collar_lite_v;
assign luld_auction_collar_lite_v = (itch_msg_type == "J");
assign itch_o.luld_auction_collar_v = luld_auction_collar_lite_v & (data_cnt_q == 'd35);
assign itch_o.luld_auction_collar_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.luld_auction_collar_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.luld_auction_collar_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.luld_auction_collar_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.luld_auction_collar_auction_collar_reference_price = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_o.luld_auction_collar_upper_auction_collar_price = data_q[LEN*23+LEN*4-1:LEN*23];
assign itch_o.luld_auction_collar_lower_auction_collar_price = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_o.luld_auction_collar_auction_collar_extension = data_q[LEN*31+LEN*4-1:LEN*31];

logic operational_halt_lite_v;
assign operational_halt_lite_v = (itch_msg_type == "h");
assign itch_o.operational_halt_v = operational_halt_lite_v & (data_cnt_q == 'd21);
assign itch_o.operational_halt_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.operational_halt_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.operational_halt_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.operational_halt_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.operational_halt_market_code = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_o.operational_halt_operational_halt_action = data_q[LEN*20+LEN*1-1:LEN*20];

logic add_order_lite_v;
assign add_order_lite_v = (itch_msg_type == "A");
assign itch_o.add_order_v = add_order_lite_v & (data_cnt_q == 'd36);
assign itch_o.add_order_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.add_order_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.add_order_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.add_order_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.add_order_buy_sell_indicator = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_o.add_order_shares = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_o.add_order_stock = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_o.add_order_price = data_q[LEN*32+LEN*4-1:LEN*32];

logic add_order_with_mpid_lite_v;
assign add_order_with_mpid_lite_v = (itch_msg_type == "F");
assign itch_o.add_order_with_mpid_v = add_order_with_mpid_lite_v & (data_cnt_q == 'd40);
assign itch_o.add_order_with_mpid_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.add_order_with_mpid_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.add_order_with_mpid_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.add_order_with_mpid_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.add_order_with_mpid_buy_sell_indicator = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_o.add_order_with_mpid_shares = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_o.add_order_with_mpid_stock = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_o.add_order_with_mpid_price = data_q[LEN*32+LEN*4-1:LEN*32];
assign itch_o.add_order_with_mpid_attribution = data_q[LEN*36+LEN*4-1:LEN*36];

logic order_executed_lite_v;
assign order_executed_lite_v = (itch_msg_type == "E");
assign itch_o.order_executed_v = order_executed_lite_v & (data_cnt_q == 'd31);
assign itch_o.order_executed_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.order_executed_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.order_executed_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.order_executed_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.order_executed_executed_shares = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_o.order_executed_match_number = data_q[LEN*23+LEN*8-1:LEN*23];

logic order_executed_with_price_lite_v;
assign order_executed_with_price_lite_v = (itch_msg_type == "C");
assign itch_o.order_executed_with_price_v = order_executed_with_price_lite_v & (data_cnt_q == 'd36);
assign itch_o.order_executed_with_price_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.order_executed_with_price_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.order_executed_with_price_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.order_executed_with_price_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.order_executed_with_price_executed_shares = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_o.order_executed_with_price_match_number = data_q[LEN*23+LEN*8-1:LEN*23];
assign itch_o.order_executed_with_price_printable = data_q[LEN*31+LEN*1-1:LEN*31];
assign itch_o.order_executed_with_price_execution_price = data_q[LEN*32+LEN*4-1:LEN*32];

logic order_cancel_lite_v;
assign order_cancel_lite_v = (itch_msg_type == "X");
assign itch_o.order_cancel_v = order_cancel_lite_v & (data_cnt_q == 'd23);
assign itch_o.order_cancel_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.order_cancel_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.order_cancel_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.order_cancel_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.order_cancel_cancelled_shares = data_q[LEN*19+LEN*4-1:LEN*19];

logic order_delete_lite_v;
assign order_delete_lite_v = (itch_msg_type == "D");
assign itch_o.order_delete_v = order_delete_lite_v & (data_cnt_q == 'd19);
assign itch_o.order_delete_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.order_delete_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.order_delete_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.order_delete_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];

logic order_replace_lite_v;
assign order_replace_lite_v = (itch_msg_type == "U");
assign itch_o.order_replace_v = order_replace_lite_v & (data_cnt_q == 'd35);
assign itch_o.order_replace_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.order_replace_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.order_replace_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.order_replace_original_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.order_replace_new_order_reference_number = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_o.order_replace_shares = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_o.order_replace_price = data_q[LEN*31+LEN*4-1:LEN*31];

logic trade_lite_v;
assign trade_lite_v = (itch_msg_type == "P");
assign itch_o.trade_v = trade_lite_v & (data_cnt_q == 'd44);
assign itch_o.trade_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.trade_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.trade_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.trade_order_reference_number = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.trade_buy_sell_indicator = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_o.trade_shares = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_o.trade_stock = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_o.trade_price = data_q[LEN*32+LEN*4-1:LEN*32];
assign itch_o.trade_match_number = data_q[LEN*36+LEN*8-1:LEN*36];

logic cross_trade_lite_v;
assign cross_trade_lite_v = (itch_msg_type == "Q");
assign itch_o.cross_trade_v = cross_trade_lite_v & (data_cnt_q == 'd40);
assign itch_o.cross_trade_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.cross_trade_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.cross_trade_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.cross_trade_shares = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.cross_trade_stock = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_o.cross_trade_cross_price = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_o.cross_trade_match_number = data_q[LEN*31+LEN*8-1:LEN*31];
assign itch_o.cross_trade_cross_type = data_q[LEN*39+LEN*1-1:LEN*39];

logic broken_trade_lite_v;
assign broken_trade_lite_v = (itch_msg_type == "B");
assign itch_o.broken_trade_v = broken_trade_lite_v & (data_cnt_q == 'd19);
assign itch_o.broken_trade_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.broken_trade_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.broken_trade_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.broken_trade_match_number = data_q[LEN*11+LEN*8-1:LEN*11];

logic net_order_imbalance_indicator_lite_v;
assign net_order_imbalance_indicator_lite_v = (itch_msg_type == "I");
assign itch_o.net_order_imbalance_indicator_v = net_order_imbalance_indicator_lite_v & (data_cnt_q == 'd50);
assign itch_o.net_order_imbalance_indicator_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.net_order_imbalance_indicator_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.net_order_imbalance_indicator_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.net_order_imbalance_indicator_paired_shares = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.net_order_imbalance_indicator_imbalance_shares = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_o.net_order_imbalance_indicator_imbalance_direction = data_q[LEN*27+LEN*1-1:LEN*27];
assign itch_o.net_order_imbalance_indicator_stock = data_q[LEN*28+LEN*8-1:LEN*28];
assign itch_o.net_order_imbalance_indicator_far_price = data_q[LEN*36+LEN*4-1:LEN*36];
assign itch_o.net_order_imbalance_indicator_near_price = data_q[LEN*40+LEN*4-1:LEN*40];
assign itch_o.net_order_imbalance_indicator_current_reference_price = data_q[LEN*44+LEN*4-1:LEN*44];
assign itch_o.net_order_imbalance_indicator_cross_type = data_q[LEN*48+LEN*1-1:LEN*48];
assign itch_o.net_order_imbalance_indicator_price_variation_indicator = data_q[LEN*49+LEN*1-1:LEN*49];

logic retail_price_improvement_indicator_lite_v;
assign retail_price_improvement_indicator_lite_v = (itch_msg_type == "N");
assign itch_o.retail_price_improvement_indicator_v = retail_price_improvement_indicator_lite_v & (data_cnt_q == 'd20);
assign itch_o.retail_price_improvement_indicator_stock_locate = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_o.retail_price_improvement_indicator_tracking_number = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_o.retail_price_improvement_indicator_timestamp = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_o.retail_price_improvement_indicator_stock = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_o.retail_price_improvement_indicator_interest_flag = data_q[LEN*19+LEN*1-1:LEN*19];

logic end_of_snapshot_lite_v;
assign end_of_snapshot_lite_v = (itch_msg_type == "G");
assign itch_o.end_of_snapshot_v = end_of_snapshot_lite_v & (data_cnt_q == 'd21);
assign itch_o.end_of_snapshot_sequence_number = data_q[LEN*1+LEN*20-1:LEN*1];

`ifdef EARLY
assign early_o.system_event_early_v = system_event_lite_v & (data_cnt_q == 'd1);
assign early_o.system_event_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.system_event_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.system_event_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.system_event_event_code_early_lite_v = data_cnt_q >= 'd12;

assign early_o.stock_directory_early_v = stock_directory_lite_v & (data_cnt_q == 'd1);
assign early_o.stock_directory_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.stock_directory_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.stock_directory_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.stock_directory_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.stock_directory_market_category_early_lite_v = data_cnt_q >= 'd20;
assign early_o.stock_directory_financial_status_indicator_early_lite_v = data_cnt_q >= 'd21;
assign early_o.stock_directory_round_lot_size_early_lite_v = data_cnt_q >= 'd25;
assign early_o.stock_directory_round_lots_only_early_lite_v = data_cnt_q >= 'd26;
assign early_o.stock_directory_issue_classification_early_lite_v = data_cnt_q >= 'd27;
assign early_o.stock_directory_issue_sub_type_early_lite_v = data_cnt_q >= 'd29;
assign early_o.stock_directory_authenticity_early_lite_v = data_cnt_q >= 'd30;
assign early_o.stock_directory_short_sale_threshold_indicator_early_lite_v = data_cnt_q >= 'd31;
assign early_o.stock_directory_ipo_flag_early_lite_v = data_cnt_q >= 'd32;
assign early_o.stock_directory_luld_reference_price_tier_early_lite_v = data_cnt_q >= 'd33;
assign early_o.stock_directory_etp_flag_early_lite_v = data_cnt_q >= 'd34;
assign early_o.stock_directory_etp_leverage_factor_early_lite_v = data_cnt_q >= 'd38;
assign early_o.stock_directory_inverse_indicator_early_lite_v = data_cnt_q >= 'd39;

assign early_o.stock_trading_action_early_v = stock_trading_action_lite_v & (data_cnt_q == 'd1);
assign early_o.stock_trading_action_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.stock_trading_action_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.stock_trading_action_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.stock_trading_action_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.stock_trading_action_trading_state_early_lite_v = data_cnt_q >= 'd20;
assign early_o.stock_trading_action_reserved_early_lite_v = data_cnt_q >= 'd21;
assign early_o.stock_trading_action_reason_early_lite_v = data_cnt_q >= 'd25;

assign early_o.reg_sho_restriction_early_v = reg_sho_restriction_lite_v & (data_cnt_q == 'd1);
assign early_o.reg_sho_restriction_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.reg_sho_restriction_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.reg_sho_restriction_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.reg_sho_restriction_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.reg_sho_restriction_reg_sho_action_early_lite_v = data_cnt_q >= 'd20;

assign early_o.market_participant_position_early_v = market_participant_position_lite_v & (data_cnt_q == 'd1);
assign early_o.market_participant_position_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.market_participant_position_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.market_participant_position_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.market_participant_position_mpid_early_lite_v = data_cnt_q >= 'd15;
assign early_o.market_participant_position_stock_early_lite_v = data_cnt_q >= 'd23;
assign early_o.market_participant_position_primary_market_maker_early_lite_v = data_cnt_q >= 'd24;
assign early_o.market_participant_position_market_maker_mode_early_lite_v = data_cnt_q >= 'd25;
assign early_o.market_participant_position_market_participant_state_early_lite_v = data_cnt_q >= 'd26;

assign early_o.mwcb_decline_level_early_v = mwcb_decline_level_lite_v & (data_cnt_q == 'd1);
assign early_o.mwcb_decline_level_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.mwcb_decline_level_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.mwcb_decline_level_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.mwcb_decline_level_level_1_early_lite_v = data_cnt_q >= 'd19;
assign early_o.mwcb_decline_level_level_2_early_lite_v = data_cnt_q >= 'd27;
assign early_o.mwcb_decline_level_level_3_early_lite_v = data_cnt_q >= 'd35;

assign early_o.mwcb_status_early_v = mwcb_status_lite_v & (data_cnt_q == 'd1);
assign early_o.mwcb_status_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.mwcb_status_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.mwcb_status_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.mwcb_status_breached_level_early_lite_v = data_cnt_q >= 'd12;

assign early_o.ipo_quoting_period_update_early_v = ipo_quoting_period_update_lite_v & (data_cnt_q == 'd1);
assign early_o.ipo_quoting_period_update_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.ipo_quoting_period_update_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.ipo_quoting_period_update_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.ipo_quoting_period_update_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.ipo_quoting_period_update_ipo_quotation_release_time_early_lite_v = data_cnt_q >= 'd23;
assign early_o.ipo_quoting_period_update_ipo_quotation_release_qualifier_early_lite_v = data_cnt_q >= 'd24;
assign early_o.ipo_quoting_period_update_ipo_price_early_lite_v = data_cnt_q >= 'd28;

assign early_o.luld_auction_collar_early_v = luld_auction_collar_lite_v & (data_cnt_q == 'd1);
assign early_o.luld_auction_collar_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.luld_auction_collar_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.luld_auction_collar_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.luld_auction_collar_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.luld_auction_collar_auction_collar_reference_price_early_lite_v = data_cnt_q >= 'd23;
assign early_o.luld_auction_collar_upper_auction_collar_price_early_lite_v = data_cnt_q >= 'd27;
assign early_o.luld_auction_collar_lower_auction_collar_price_early_lite_v = data_cnt_q >= 'd31;
assign early_o.luld_auction_collar_auction_collar_extension_early_lite_v = data_cnt_q >= 'd35;

assign early_o.operational_halt_early_v = operational_halt_lite_v & (data_cnt_q == 'd1);
assign early_o.operational_halt_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.operational_halt_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.operational_halt_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.operational_halt_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.operational_halt_market_code_early_lite_v = data_cnt_q >= 'd20;
assign early_o.operational_halt_operational_halt_action_early_lite_v = data_cnt_q >= 'd21;

assign early_o.add_order_early_v = add_order_lite_v & (data_cnt_q == 'd1);
assign early_o.add_order_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.add_order_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.add_order_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.add_order_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.add_order_buy_sell_indicator_early_lite_v = data_cnt_q >= 'd20;
assign early_o.add_order_shares_early_lite_v = data_cnt_q >= 'd24;
assign early_o.add_order_stock_early_lite_v = data_cnt_q >= 'd32;
assign early_o.add_order_price_early_lite_v = data_cnt_q >= 'd36;

assign early_o.add_order_with_mpid_early_v = add_order_with_mpid_lite_v & (data_cnt_q == 'd1);
assign early_o.add_order_with_mpid_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.add_order_with_mpid_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.add_order_with_mpid_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.add_order_with_mpid_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.add_order_with_mpid_buy_sell_indicator_early_lite_v = data_cnt_q >= 'd20;
assign early_o.add_order_with_mpid_shares_early_lite_v = data_cnt_q >= 'd24;
assign early_o.add_order_with_mpid_stock_early_lite_v = data_cnt_q >= 'd32;
assign early_o.add_order_with_mpid_price_early_lite_v = data_cnt_q >= 'd36;
assign early_o.add_order_with_mpid_attribution_early_lite_v = data_cnt_q >= 'd40;

assign early_o.order_executed_early_v = order_executed_lite_v & (data_cnt_q == 'd1);
assign early_o.order_executed_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_executed_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_executed_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_executed_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_executed_executed_shares_early_lite_v = data_cnt_q >= 'd23;
assign early_o.order_executed_match_number_early_lite_v = data_cnt_q >= 'd31;

assign early_o.order_executed_with_price_early_v = order_executed_with_price_lite_v & (data_cnt_q == 'd1);
assign early_o.order_executed_with_price_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_executed_with_price_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_executed_with_price_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_executed_with_price_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_executed_with_price_executed_shares_early_lite_v = data_cnt_q >= 'd23;
assign early_o.order_executed_with_price_match_number_early_lite_v = data_cnt_q >= 'd31;
assign early_o.order_executed_with_price_printable_early_lite_v = data_cnt_q >= 'd32;
assign early_o.order_executed_with_price_execution_price_early_lite_v = data_cnt_q >= 'd36;

assign early_o.order_cancel_early_v = order_cancel_lite_v & (data_cnt_q == 'd1);
assign early_o.order_cancel_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_cancel_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_cancel_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_cancel_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_cancel_cancelled_shares_early_lite_v = data_cnt_q >= 'd23;

assign early_o.order_delete_early_v = order_delete_lite_v & (data_cnt_q == 'd1);
assign early_o.order_delete_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_delete_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_delete_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_delete_order_reference_number_early_lite_v = data_cnt_q >= 'd19;

assign early_o.order_replace_early_v = order_replace_lite_v & (data_cnt_q == 'd1);
assign early_o.order_replace_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_replace_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_replace_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_replace_original_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_replace_new_order_reference_number_early_lite_v = data_cnt_q >= 'd27;
assign early_o.order_replace_shares_early_lite_v = data_cnt_q >= 'd31;
assign early_o.order_replace_price_early_lite_v = data_cnt_q >= 'd35;

assign early_o.trade_early_v = trade_lite_v & (data_cnt_q == 'd1);
assign early_o.trade_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.trade_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.trade_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.trade_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.trade_buy_sell_indicator_early_lite_v = data_cnt_q >= 'd20;
assign early_o.trade_shares_early_lite_v = data_cnt_q >= 'd24;
assign early_o.trade_stock_early_lite_v = data_cnt_q >= 'd32;
assign early_o.trade_price_early_lite_v = data_cnt_q >= 'd36;
assign early_o.trade_match_number_early_lite_v = data_cnt_q >= 'd44;

assign early_o.cross_trade_early_v = cross_trade_lite_v & (data_cnt_q == 'd1);
assign early_o.cross_trade_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.cross_trade_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.cross_trade_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.cross_trade_shares_early_lite_v = data_cnt_q >= 'd19;
assign early_o.cross_trade_stock_early_lite_v = data_cnt_q >= 'd27;
assign early_o.cross_trade_cross_price_early_lite_v = data_cnt_q >= 'd31;
assign early_o.cross_trade_match_number_early_lite_v = data_cnt_q >= 'd39;
assign early_o.cross_trade_cross_type_early_lite_v = data_cnt_q >= 'd40;

assign early_o.broken_trade_early_v = broken_trade_lite_v & (data_cnt_q == 'd1);
assign early_o.broken_trade_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.broken_trade_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.broken_trade_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.broken_trade_match_number_early_lite_v = data_cnt_q >= 'd19;

assign early_o.net_order_imbalance_indicator_early_v = net_order_imbalance_indicator_lite_v & (data_cnt_q == 'd1);
assign early_o.net_order_imbalance_indicator_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.net_order_imbalance_indicator_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.net_order_imbalance_indicator_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.net_order_imbalance_indicator_paired_shares_early_lite_v = data_cnt_q >= 'd19;
assign early_o.net_order_imbalance_indicator_imbalance_shares_early_lite_v = data_cnt_q >= 'd27;
assign early_o.net_order_imbalance_indicator_imbalance_direction_early_lite_v = data_cnt_q >= 'd28;
assign early_o.net_order_imbalance_indicator_stock_early_lite_v = data_cnt_q >= 'd36;
assign early_o.net_order_imbalance_indicator_far_price_early_lite_v = data_cnt_q >= 'd40;
assign early_o.net_order_imbalance_indicator_near_price_early_lite_v = data_cnt_q >= 'd44;
assign early_o.net_order_imbalance_indicator_current_reference_price_early_lite_v = data_cnt_q >= 'd48;
assign early_o.net_order_imbalance_indicator_cross_type_early_lite_v = data_cnt_q >= 'd49;
assign early_o.net_order_imbalance_indicator_price_variation_indicator_early_lite_v = data_cnt_q >= 'd50;

assign early_o.retail_price_improvement_indicator_early_v = retail_price_improvement_indicator_lite_v & (data_cnt_q == 'd1);
assign early_o.retail_price_improvement_indicator_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.retail_price_improvement_indicator_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.retail_price_improvement_indicator_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.retail_price_improvement_indicator_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.retail_price_improvement_indicator_interest_flag_early_lite_v = data_cnt_q >= 'd20;

assign early_o.end_of_snapshot_early_v = end_of_snapshot_lite_v & (data_cnt_q == 'd1);
assign early_o.end_of_snapshot_sequence_number_early_lite_v = data_cnt_q >= 'd21;
`endif

`ifdef DEBUG_ID
// debug id
assign debug_id_next = debug_id_i;
assign debug_id_en   = valid_i & start_i;
always @(posedge clk) begin
	if ( debug_id_en ) begin
		debug_id_q <= debug_id_next;
	end
end
assign debug_id_o    = debug_id_q;
`endif
// message type : allways at offset 0
assign itch_msg_type = data_q[LEN-1:0];
// message has been sent
assign itch_msg_sent = ( itch_o.system_event_v 
					 | itch_o.stock_directory_v
					 | itch_o.stock_trading_action_v 
					 | itch_o.reg_sho_restriction_v
					 | itch_o.market_participant_position_v
					 | itch_o.mwcb_decline_level_v
					 | itch_o.mwcb_status_v
					 | itch_o.ipo_quoting_period_update_v
					 | itch_o.luld_auction_collar_v
					 | itch_o.operational_halt_v
					 | itch_o.add_order_v
					 | itch_o.add_order_with_mpid_v
					 | itch_o.order_executed_v
					 | itch_o.order_executed_with_price_v
					 | itch_o.order_cancel_v
					 | itch_o.order_delete_v
					 | itch_o.order_replace_v
					 | itch_o.trade_v
					 | itch_o.cross_trade_v
					 | itch_o.broken_trade_v
					 | itch_o.net_order_imbalance_indicator_v
					 | itch_o.retail_price_improvement_indicator_v 
`ifdef GLIMPSE
					 | itch_o.end_of_snapshot_v
`endif
 ); 

// output
// itch message assignement logic

`ifdef FORMAL
initial begin
	a_reset : assume( ~nreset);

	//a_cnt_not_unknown : assume ( ~$isunknown( data_cnt_q ));
end

always @(posedge clk) begin
	if ( nreset ) begin
		// mold input behavior
		a_v_not_unknown : assume( ~$isunknown( valid_i));
		a_data_not_unknown : assume( ~valid_i | ( valid_i & ~$isunknown( start_i | |data_i ) ));
		// should never receive more than the max expected number of packets
		a_data_cnt_overflow : assume ( ~data_cnt_add_overflow );

		// xcheck
		sva_xcheck_data_cnt : assert ( ~$isunknown( |data_cnt_q ));
		for(int unsigned x = 0; x < PL_MAX_N; x++ ) begin 
			// assert( ~(data_cnt_q == x) | ( (data_cnt_q == x ) & ~$isunknown( data_q[AXI_DATA_W*x+AXI_DATA_W-1:AXI_DATA_W*x])));
		end
		sva_data_en_onehot0 : assert ( $onehot0(data_en));

		// itch 
		sva_xcheck_itch_system_event_v_o : assert( ~$isunknown(itch_system_event_v_o));
		sva_xcheck_itch_system_event_data : assert( ~itch_system_event_v_o | (itch_system_event_v_o & ~$isunknown((|itch_system_event_stock_locate_o | |itch_system_event_tracking_number_o | |itch_system_event_timestamp_o | |itch_system_event_event_code_o))));
		
		sva_xcheck_itch_stock_directory_v_o : assert( ~$isunknown(itch_stock_directory_v_o));
		sva_xcheck_itch_stock_directory_data : assert( ~itch_stock_directory_v_o | (itch_stock_directory_v_o & ~$isunknown((|itch_stock_directory_stock_locate_o | |itch_stock_directory_tracking_number_o | |itch_stock_directory_timestamp_o | |itch_stock_directory_stock_o | |itch_stock_directory_market_category_o | |itch_stock_directory_financial_status_indicator_o | |itch_stock_directory_round_lot_size_o | |itch_stock_directory_round_lots_only_o | |itch_stock_directory_issue_classification_o | |itch_stock_directory_issue_sub_type_o | |itch_stock_directory_authenticity_o | |itch_stock_directory_short_sale_threshold_indicator_o | |itch_stock_directory_ipo_flag_o | |itch_stock_directory_luld_reference_price_tier_o | |itch_stock_directory_etp_flag_o | |itch_stock_directory_etp_leverage_factor_o | |itch_stock_directory_inverse_indicator_o))));
		
		sva_xcheck_itch_stock_trading_action_v_o : assert( ~$isunknown(itch_stock_trading_action_v_o));
		sva_xcheck_itch_stock_trading_action_data : assert( ~itch_stock_trading_action_v_o | (itch_stock_trading_action_v_o & ~$isunknown((|itch_stock_trading_action_stock_locate_o | |itch_stock_trading_action_tracking_number_o | |itch_stock_trading_action_timestamp_o | |itch_stock_trading_action_stock_o | |itch_stock_trading_action_trading_state_o | |itch_stock_trading_action_reserved_o | |itch_stock_trading_action_reason_o))));
		
		sva_xcheck_itch_reg_sho_restriction_v_o : assert( ~$isunknown(itch_reg_sho_restriction_v_o));
		sva_xcheck_itch_reg_sho_restriction_data : assert( ~itch_reg_sho_restriction_v_o | (itch_reg_sho_restriction_v_o & ~$isunknown((|itch_reg_sho_restriction_stock_locate_o | |itch_reg_sho_restriction_tracking_number_o | |itch_reg_sho_restriction_timestamp_o | |itch_reg_sho_restriction_stock_o | |itch_reg_sho_restriction_reg_sho_action_o))));
		
		sva_xcheck_itch_market_participant_position_v_o : assert( ~$isunknown(itch_market_participant_position_v_o));
		sva_xcheck_itch_market_participant_position_data : assert( ~itch_market_participant_position_v_o | (itch_market_participant_position_v_o & ~$isunknown((|itch_market_participant_position_stock_locate_o | |itch_market_participant_position_tracking_number_o | |itch_market_participant_position_timestamp_o | |itch_market_participant_position_mpid_o | |itch_market_participant_position_stock_o | |itch_market_participant_position_primary_market_maker_o | |itch_market_participant_position_market_maker_mode_o | |itch_market_participant_position_market_participant_state_o))));
		
		sva_xcheck_itch_mwcb_decline_level_v_o : assert( ~$isunknown(itch_mwcb_decline_level_v_o));
		sva_xcheck_itch_mwcb_decline_level_data : assert( ~itch_mwcb_decline_level_v_o | (itch_mwcb_decline_level_v_o & ~$isunknown((|itch_mwcb_decline_level_stock_locate_o | |itch_mwcb_decline_level_tracking_number_o | |itch_mwcb_decline_level_timestamp_o | |itch_mwcb_decline_level_level_1_o | |itch_mwcb_decline_level_level_2_o | |itch_mwcb_decline_level_level_3_o))));
		
		sva_xcheck_itch_mwcb_status_v_o : assert( ~$isunknown(itch_mwcb_status_v_o));
		sva_xcheck_itch_mwcb_status_data : assert( ~itch_mwcb_status_v_o | (itch_mwcb_status_v_o & ~$isunknown((|itch_mwcb_status_stock_locate_o | |itch_mwcb_status_tracking_number_o | |itch_mwcb_status_timestamp_o | |itch_mwcb_status_breached_level_o))));
		
		sva_xcheck_itch_ipo_quoting_period_update_v_o : assert( ~$isunknown(itch_ipo_quoting_period_update_v_o));
		sva_xcheck_itch_ipo_quoting_period_update_data : assert( ~itch_ipo_quoting_period_update_v_o | (itch_ipo_quoting_period_update_v_o & ~$isunknown((|itch_ipo_quoting_period_update_stock_locate_o | |itch_ipo_quoting_period_update_tracking_number_o | |itch_ipo_quoting_period_update_timestamp_o | |itch_ipo_quoting_period_update_stock_o | |itch_ipo_quoting_period_update_ipo_quotation_release_time_o | |itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o | |itch_ipo_quoting_period_update_ipo_price_o))));
		
		sva_xcheck_itch_luld_auction_collar_v_o : assert( ~$isunknown(itch_luld_auction_collar_v_o));
		sva_xcheck_itch_luld_auction_collar_data : assert( ~itch_luld_auction_collar_v_o | (itch_luld_auction_collar_v_o & ~$isunknown((|itch_luld_auction_collar_stock_locate_o | |itch_luld_auction_collar_tracking_number_o | |itch_luld_auction_collar_timestamp_o | |itch_luld_auction_collar_stock_o | |itch_luld_auction_collar_auction_collar_reference_price_o | |itch_luld_auction_collar_upper_auction_collar_price_o | |itch_luld_auction_collar_lower_auction_collar_price_o | |itch_luld_auction_collar_auction_collar_extension_o))));
		
		sva_xcheck_itch_operational_halt_v_o : assert( ~$isunknown(itch_operational_halt_v_o));
		sva_xcheck_itch_operational_halt_data : assert( ~itch_operational_halt_v_o | (itch_operational_halt_v_o & ~$isunknown((|itch_operational_halt_stock_locate_o | |itch_operational_halt_tracking_number_o | |itch_operational_halt_timestamp_o | |itch_operational_halt_stock_o | |itch_operational_halt_market_code_o | |itch_operational_halt_operational_halt_action_o))));
		
		sva_xcheck_itch_add_order_v_o : assert( ~$isunknown(itch_add_order_v_o));
		sva_xcheck_itch_add_order_data : assert( ~itch_add_order_v_o | (itch_add_order_v_o & ~$isunknown((|itch_add_order_stock_locate_o | |itch_add_order_tracking_number_o | |itch_add_order_timestamp_o | |itch_add_order_order_reference_number_o | |itch_add_order_buy_sell_indicator_o | |itch_add_order_shares_o | |itch_add_order_stock_o | |itch_add_order_price_o))));
		
		sva_xcheck_itch_add_order_with_mpid_v_o : assert( ~$isunknown(itch_add_order_with_mpid_v_o));
		sva_xcheck_itch_add_order_with_mpid_data : assert( ~itch_add_order_with_mpid_v_o | (itch_add_order_with_mpid_v_o & ~$isunknown((|itch_add_order_with_mpid_stock_locate_o | |itch_add_order_with_mpid_tracking_number_o | |itch_add_order_with_mpid_timestamp_o | |itch_add_order_with_mpid_order_reference_number_o | |itch_add_order_with_mpid_buy_sell_indicator_o | |itch_add_order_with_mpid_shares_o | |itch_add_order_with_mpid_stock_o | |itch_add_order_with_mpid_price_o | |itch_add_order_with_mpid_attribution_o))));
		
		sva_xcheck_itch_order_executed_v_o : assert( ~$isunknown(itch_order_executed_v_o));
		sva_xcheck_itch_order_executed_data : assert( ~itch_order_executed_v_o | (itch_order_executed_v_o & ~$isunknown((|itch_order_executed_stock_locate_o | |itch_order_executed_tracking_number_o | |itch_order_executed_timestamp_o | |itch_order_executed_order_reference_number_o | |itch_order_executed_executed_shares_o | |itch_order_executed_match_number_o))));
		
		sva_xcheck_itch_order_executed_with_price_v_o : assert( ~$isunknown(itch_order_executed_with_price_v_o));
		sva_xcheck_itch_order_executed_with_price_data : assert( ~itch_order_executed_with_price_v_o | (itch_order_executed_with_price_v_o & ~$isunknown((|itch_order_executed_with_price_stock_locate_o | |itch_order_executed_with_price_tracking_number_o | |itch_order_executed_with_price_timestamp_o | |itch_order_executed_with_price_order_reference_number_o | |itch_order_executed_with_price_executed_shares_o | |itch_order_executed_with_price_match_number_o | |itch_order_executed_with_price_printable_o | |itch_order_executed_with_price_execution_price_o))));
		
		sva_xcheck_itch_order_cancel_v_o : assert( ~$isunknown(itch_order_cancel_v_o));
		sva_xcheck_itch_order_cancel_data : assert( ~itch_order_cancel_v_o | (itch_order_cancel_v_o & ~$isunknown((|itch_order_cancel_stock_locate_o | |itch_order_cancel_tracking_number_o | |itch_order_cancel_timestamp_o | |itch_order_cancel_order_reference_number_o | |itch_order_cancel_cancelled_shares_o))));
		
		sva_xcheck_itch_order_delete_v_o : assert( ~$isunknown(itch_order_delete_v_o));
		sva_xcheck_itch_order_delete_data : assert( ~itch_order_delete_v_o | (itch_order_delete_v_o & ~$isunknown((|itch_order_delete_stock_locate_o | |itch_order_delete_tracking_number_o | |itch_order_delete_timestamp_o | |itch_order_delete_order_reference_number_o))));
		
		sva_xcheck_itch_order_replace_v_o : assert( ~$isunknown(itch_order_replace_v_o));
		sva_xcheck_itch_order_replace_data : assert( ~itch_order_replace_v_o | (itch_order_replace_v_o & ~$isunknown((|itch_order_replace_stock_locate_o | |itch_order_replace_tracking_number_o | |itch_order_replace_timestamp_o | |itch_order_replace_original_order_reference_number_o | |itch_order_replace_new_order_reference_number_o | |itch_order_replace_shares_o | |itch_order_replace_price_o))));
		
		sva_xcheck_itch_trade_v_o : assert( ~$isunknown(itch_trade_v_o));
		sva_xcheck_itch_trade_data : assert( ~itch_trade_v_o | (itch_trade_v_o & ~$isunknown((|itch_trade_stock_locate_o | |itch_trade_tracking_number_o | |itch_trade_timestamp_o | |itch_trade_order_reference_number_o | |itch_trade_buy_sell_indicator_o | |itch_trade_shares_o | |itch_trade_stock_o | |itch_trade_price_o | |itch_trade_match_number_o))));
		
		sva_xcheck_itch_cross_trade_v_o : assert( ~$isunknown(itch_cross_trade_v_o));
		sva_xcheck_itch_cross_trade_data : assert( ~itch_cross_trade_v_o | (itch_cross_trade_v_o & ~$isunknown((|itch_cross_trade_stock_locate_o | |itch_cross_trade_tracking_number_o | |itch_cross_trade_timestamp_o | |itch_cross_trade_shares_o | |itch_cross_trade_stock_o | |itch_cross_trade_cross_price_o | |itch_cross_trade_match_number_o | |itch_cross_trade_cross_type_o))));
		
		sva_xcheck_itch_broken_trade_v_o : assert( ~$isunknown(itch_broken_trade_v_o));
		sva_xcheck_itch_broken_trade_data : assert( ~itch_broken_trade_v_o | (itch_broken_trade_v_o & ~$isunknown((|itch_broken_trade_stock_locate_o | |itch_broken_trade_tracking_number_o | |itch_broken_trade_timestamp_o | |itch_broken_trade_match_number_o))));
		
		sva_xcheck_itch_net_order_imbalance_indicator_v_o : assert( ~$isunknown(itch_net_order_imbalance_indicator_v_o));
		sva_xcheck_itch_net_order_imbalance_indicator_data : assert( ~itch_net_order_imbalance_indicator_v_o | (itch_net_order_imbalance_indicator_v_o & ~$isunknown((|itch_net_order_imbalance_indicator_stock_locate_o | |itch_net_order_imbalance_indicator_tracking_number_o | |itch_net_order_imbalance_indicator_timestamp_o | |itch_net_order_imbalance_indicator_paired_shares_o | |itch_net_order_imbalance_indicator_imbalance_shares_o | |itch_net_order_imbalance_indicator_imbalance_direction_o | |itch_net_order_imbalance_indicator_stock_o | |itch_net_order_imbalance_indicator_far_price_o | |itch_net_order_imbalance_indicator_near_price_o | |itch_net_order_imbalance_indicator_current_reference_price_o | |itch_net_order_imbalance_indicator_cross_type_o | |itch_net_order_imbalance_indicator_price_variation_indicator_o))));
		
		sva_xcheck_itch_retail_price_improvement_indicator_v_o : assert( ~$isunknown(itch_retail_price_improvement_indicator_v_o));
		sva_xcheck_itch_retail_price_improvement_indicator_data : assert( ~itch_retail_price_improvement_indicator_v_o | (itch_retail_price_improvement_indicator_v_o & ~$isunknown((|itch_retail_price_improvement_indicator_stock_locate_o | |itch_retail_price_improvement_indicator_tracking_number_o | |itch_retail_price_improvement_indicator_timestamp_o | |itch_retail_price_improvement_indicator_stock_o | |itch_retail_price_improvement_indicator_interest_flag_o))));
		`ifdef GLIMPSE	
		sva_xcheck_itch_end_of_snapshot_v_o : assert( ~$isunknown(itch_end_of_snapshot_v_o));
		sva_xcheck_itch_end_of_snapshot_data : assert( ~itch_end_of_snapshot_v_o | (itch_end_of_snapshot_v_o & ~$isunknown((|itch_end_of_snapshot_sequence_number_o))));
		`endif
		sva_itch_msg_valid_onehot0 : assert( $onehot0({itch_system_event_v_o,itch_stock_directory_v_o,itch_stock_trading_action_v_o,itch_reg_sho_restriction_v_o,itch_market_participant_position_v_o,itch_mwcb_decline_level_v_o,itch_mwcb_status_v_o,itch_ipo_quoting_period_update_v_o,itch_luld_auction_collar_v_o,itch_operational_halt_v_o,itch_add_order_v_o,itch_add_order_with_mpid_v_o,itch_order_executed_v_o,itch_order_executed_with_price_v_o,itch_order_cancel_v_o,itch_order_delete_v_o,itch_order_replace_v_o,itch_trade_v_o,itch_cross_trade_v_o,itch_broken_trade_v_o,itch_net_order_imbalance_indicator_v_o,itch_retail_price_improvement_indicator_v_o
		`ifdef GLIMPSE
		,itch_end_of_snapshot_v_o
		`endif
		}));	
	end
end

`endif
endmodule
