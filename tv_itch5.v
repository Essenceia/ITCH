/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

module tv_itch5 #(
	`ifdef MOLD_MSD_IDS
	parameter SID_W     = 80,
	parameter SEQ_NUM_W = 64
	`endif	

	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = AXI_DATA_W / 8,
	
	// itch data
	parameter LEN = 8,

	parameter MSG_MAX_W = 50*LEN,// maximum length an itch message ( net order imbalance ) 
	parameter CNT_MAX = 7,// $ceil(MSG_MAX_W / AXI_DATA_W) // maxium number of payloads that need to be received for the longest itch message 
	parameter CNT_MAX_W = $clog2(CNT_MAX)
)(
	input clk,
	input nreset,

	//message
	input valid_i,
	input start_i,
	input [AXI_DATA_W-1:0] data_i,

	`ifdef MOLD_MSD_IDS
	input [SID_W-1:0]     mold_sid_i,
	input [SEQ_NUM_W-1:0] mold_seq_num_i, 
	`endif 

	output logic itch_system_event_v_o,
	output logic [2*LEN-1:0] itch_system_event_stock_locate_o,
	output logic [2*LEN-1:0] itch_system_event_tracking_number_o,
	output logic [6*LEN-1:0] itch_system_event_timestamp_o,
	output logic [1*LEN-1:0] itch_system_event_event_code_o,
	
	output logic itch_stock_directory_v_o,
	output logic [2*LEN-1:0] itch_stock_directory_stock_locate_o,
	output logic [2*LEN-1:0] itch_stock_directory_tracking_number_o,
	output logic [6*LEN-1:0] itch_stock_directory_timestamp_o,
	output logic [8*LEN-1:0] itch_stock_directory_stock_o,
	output logic [1*LEN-1:0] itch_stock_directory_market_category_o,
	output logic [1*LEN-1:0] itch_stock_directory_financial_status_indicator_o,
	output logic [4*LEN-1:0] itch_stock_directory_round_lot_size_o,
	output logic [1*LEN-1:0] itch_stock_directory_round_lots_only_o,
	output logic [1*LEN-1:0] itch_stock_directory_issue_classification_o,
	output logic [2*LEN-1:0] itch_stock_directory_issue_sub_type_o,
	output logic [1*LEN-1:0] itch_stock_directory_authenticity_o,
	output logic [1*LEN-1:0] itch_stock_directory_short_sale_threshold_indicator_o,
	output logic [1*LEN-1:0] itch_stock_directory_ipo_flag_o,
	output logic [1*LEN-1:0] itch_stock_directory_luld_reference_price_tier_o,
	output logic [1*LEN-1:0] itch_stock_directory_etp_flag_o,
	output logic [4*LEN-1:0] itch_stock_directory_etp_leverage_factor_o,
	output logic [1*LEN-1:0] itch_stock_directory_inverse_indicator_o,
	
	output logic itch_stock_trading_action_v_o,
	output logic [2*LEN-1:0] itch_stock_trading_action_stock_locate_o,
	output logic [2*LEN-1:0] itch_stock_trading_action_tracking_number_o,
	output logic [6*LEN-1:0] itch_stock_trading_action_timestamp_o,
	output logic [8*LEN-1:0] itch_stock_trading_action_stock_o,
	output logic [1*LEN-1:0] itch_stock_trading_action_trading_state_o,
	output logic [1*LEN-1:0] itch_stock_trading_action_reserved_o,
	output logic [4*LEN-1:0] itch_stock_trading_action_reason_o,
	
	output logic itch_reg_sho_restriction_v_o,
	output logic [2*LEN-1:0] itch_reg_sho_restriction_stock_locate_o,
	output logic [2*LEN-1:0] itch_reg_sho_restriction_tracking_number_o,
	output logic [6*LEN-1:0] itch_reg_sho_restriction_timestamp_o,
	output logic [8*LEN-1:0] itch_reg_sho_restriction_stock_o,
	output logic [1*LEN-1:0] itch_reg_sho_restriction_reg_sho_action_o,
	
	output logic itch_market_participant_position_v_o,
	output logic [2*LEN-1:0] itch_market_participant_position_stock_locate_o,
	output logic [2*LEN-1:0] itch_market_participant_position_tracking_number_o,
	output logic [6*LEN-1:0] itch_market_participant_position_timestamp_o,
	output logic [4*LEN-1:0] itch_market_participant_position_mpid_o,
	output logic [8*LEN-1:0] itch_market_participant_position_stock_o,
	output logic [1*LEN-1:0] itch_market_participant_position_primary_market_maker_o,
	output logic [1*LEN-1:0] itch_market_participant_position_market_maker_mode_o,
	output logic [1*LEN-1:0] itch_market_participant_position_market_participant_state_o,
	
	output logic itch_mwcb_decline_level_v_o,
	output logic [2*LEN-1:0] itch_mwcb_decline_level_stock_locate_o,
	output logic [2*LEN-1:0] itch_mwcb_decline_level_tracking_number_o,
	output logic [6*LEN-1:0] itch_mwcb_decline_level_timestamp_o,
	output logic [8*LEN-1:0] itch_mwcb_decline_level_level_1_o,
	output logic [8*LEN-1:0] itch_mwcb_decline_level_level_2_o,
	output logic [8*LEN-1:0] itch_mwcb_decline_level_level_3_o,
	
	output logic itch_mwcb_status_v_o,
	output logic [2*LEN-1:0] itch_mwcb_status_stock_locate_o,
	output logic [2*LEN-1:0] itch_mwcb_status_tracking_number_o,
	output logic [6*LEN-1:0] itch_mwcb_status_timestamp_o,
	output logic [1*LEN-1:0] itch_mwcb_status_breached_level_o,
	
	output logic itch_ipo_quoting_period_update_v_o,
	output logic [2*LEN-1:0] itch_ipo_quoting_period_update_stock_locate_o,
	output logic [2*LEN-1:0] itch_ipo_quoting_period_update_tracking_number_o,
	output logic [6*LEN-1:0] itch_ipo_quoting_period_update_timestamp_o,
	output logic [8*LEN-1:0] itch_ipo_quoting_period_update_stock_o,
	output logic [4*LEN-1:0] itch_ipo_quoting_period_update_ipo_quotation_release_time_o,
	output logic [1*LEN-1:0] itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o,
	output logic [4*LEN-1:0] itch_ipo_quoting_period_update_ipo_price_o,
	
	output logic itch_luld_auction_collar_v_o,
	output logic [2*LEN-1:0] itch_luld_auction_collar_stock_locate_o,
	output logic [2*LEN-1:0] itch_luld_auction_collar_tracking_number_o,
	output logic [6*LEN-1:0] itch_luld_auction_collar_timestamp_o,
	output logic [8*LEN-1:0] itch_luld_auction_collar_stock_o,
	output logic [4*LEN-1:0] itch_luld_auction_collar_auction_collar_reference_price_o,
	output logic [4*LEN-1:0] itch_luld_auction_collar_upper_auction_collar_price_o,
	output logic [4*LEN-1:0] itch_luld_auction_collar_lower_auction_collar_price_o,
	output logic [4*LEN-1:0] itch_luld_auction_collar_auction_collar_extension_o,
	
	output logic itch_operational_halt_v_o,
	output logic [2*LEN-1:0] itch_operational_halt_stock_locate_o,
	output logic [2*LEN-1:0] itch_operational_halt_tracking_number_o,
	output logic [6*LEN-1:0] itch_operational_halt_timestamp_o,
	output logic [8*LEN-1:0] itch_operational_halt_stock_o,
	output logic [1*LEN-1:0] itch_operational_halt_market_code_o,
	output logic [1*LEN-1:0] itch_operational_halt_operational_halt_action_o,
	
	output logic itch_add_order_v_o,
	output logic [2*LEN-1:0] itch_add_order_stock_locate_o,
	output logic [2*LEN-1:0] itch_add_order_tracking_number_o,
	output logic [6*LEN-1:0] itch_add_order_timestamp_o,
	output logic [8*LEN-1:0] itch_add_order_order_reference_number_o,
	output logic [1*LEN-1:0] itch_add_order_buy_sell_indicator_o,
	output logic [4*LEN-1:0] itch_add_order_shares_o,
	output logic [8*LEN-1:0] itch_add_order_stock_o,
	output logic [4*LEN-1:0] itch_add_order_price_o,
	
	output logic itch_add_order_with_mpid_v_o,
	output logic [2*LEN-1:0] itch_add_order_with_mpid_stock_locate_o,
	output logic [2*LEN-1:0] itch_add_order_with_mpid_tracking_number_o,
	output logic [6*LEN-1:0] itch_add_order_with_mpid_timestamp_o,
	output logic [8*LEN-1:0] itch_add_order_with_mpid_order_reference_number_o,
	output logic [1*LEN-1:0] itch_add_order_with_mpid_buy_sell_indicator_o,
	output logic [4*LEN-1:0] itch_add_order_with_mpid_shares_o,
	output logic [8*LEN-1:0] itch_add_order_with_mpid_stock_o,
	output logic [4*LEN-1:0] itch_add_order_with_mpid_price_o,
	output logic [4*LEN-1:0] itch_add_order_with_mpid_attribution_o,
	
	output logic itch_order_executed_v_o,
	output logic [2*LEN-1:0] itch_order_executed_stock_locate_o,
	output logic [2*LEN-1:0] itch_order_executed_tracking_number_o,
	output logic [6*LEN-1:0] itch_order_executed_timestamp_o,
	output logic [8*LEN-1:0] itch_order_executed_order_reference_number_o,
	output logic [4*LEN-1:0] itch_order_executed_executed_shares_o,
	output logic [8*LEN-1:0] itch_order_executed_match_number_o,
	
	output logic itch_order_executed_with_price_v_o,
	output logic [2*LEN-1:0] itch_order_executed_with_price_stock_locate_o,
	output logic [2*LEN-1:0] itch_order_executed_with_price_tracking_number_o,
	output logic [6*LEN-1:0] itch_order_executed_with_price_timestamp_o,
	output logic [8*LEN-1:0] itch_order_executed_with_price_order_reference_number_o,
	output logic [4*LEN-1:0] itch_order_executed_with_price_executed_shares_o,
	output logic [8*LEN-1:0] itch_order_executed_with_price_match_number_o,
	output logic [1*LEN-1:0] itch_order_executed_with_price_printable_o,
	output logic [4*LEN-1:0] itch_order_executed_with_price_execution_price_o,
	
	output logic itch_order_cancel_v_o,
	output logic [2*LEN-1:0] itch_order_cancel_stock_locate_o,
	output logic [2*LEN-1:0] itch_order_cancel_tracking_number_o,
	output logic [6*LEN-1:0] itch_order_cancel_timestamp_o,
	output logic [8*LEN-1:0] itch_order_cancel_order_reference_number_o,
	output logic [4*LEN-1:0] itch_order_cancel_cancelled_shares_o,
	
	output logic itch_order_delete_v_o,
	output logic [2*LEN-1:0] itch_order_delete_stock_locate_o,
	output logic [2*LEN-1:0] itch_order_delete_tracking_number_o,
	output logic [6*LEN-1:0] itch_order_delete_timestamp_o,
	output logic [8*LEN-1:0] itch_order_delete_order_reference_number_o,
	
	output logic itch_order_replace_v_o,
	output logic [2*LEN-1:0] itch_order_replace_stock_locate_o,
	output logic [2*LEN-1:0] itch_order_replace_tracking_number_o,
	output logic [6*LEN-1:0] itch_order_replace_timestamp_o,
	output logic [8*LEN-1:0] itch_order_replace_original_order_reference_number_o,
	output logic [8*LEN-1:0] itch_order_replace_new_order_reference_number_o,
	output logic [4*LEN-1:0] itch_order_replace_shares_o,
	output logic [4*LEN-1:0] itch_order_replace_price_o,
	
	output logic itch_trade_v_o,
	output logic [2*LEN-1:0] itch_trade_stock_locate_o,
	output logic [2*LEN-1:0] itch_trade_tracking_number_o,
	output logic [6*LEN-1:0] itch_trade_timestamp_o,
	output logic [8*LEN-1:0] itch_trade_order_reference_number_o,
	output logic [1*LEN-1:0] itch_trade_buy_sell_indicator_o,
	output logic [4*LEN-1:0] itch_trade_shares_o,
	output logic [8*LEN-1:0] itch_trade_stock_o,
	output logic [4*LEN-1:0] itch_trade_price_o,
	output logic [8*LEN-1:0] itch_trade_match_number_o,
	
	output logic itch_cross_trade_v_o,
	output logic [2*LEN-1:0] itch_cross_trade_stock_locate_o,
	output logic [2*LEN-1:0] itch_cross_trade_tracking_number_o,
	output logic [6*LEN-1:0] itch_cross_trade_timestamp_o,
	output logic [8*LEN-1:0] itch_cross_trade_shares_o,
	output logic [8*LEN-1:0] itch_cross_trade_stock_o,
	output logic [4*LEN-1:0] itch_cross_trade_cross_price_o,
	output logic [8*LEN-1:0] itch_cross_trade_match_number_o,
	output logic [1*LEN-1:0] itch_cross_trade_cross_type_o,
	
	output logic itch_broken_trade_v_o,
	output logic [2*LEN-1:0] itch_broken_trade_stock_locate_o,
	output logic [2*LEN-1:0] itch_broken_trade_tracking_number_o,
	output logic [6*LEN-1:0] itch_broken_trade_timestamp_o,
	output logic [8*LEN-1:0] itch_broken_trade_match_number_o,
	
	output logic itch_net_order_imbalance_indicator_v_o,
	output logic [2*LEN-1:0] itch_net_order_imbalance_indicator_stock_locate_o,
	output logic [2*LEN-1:0] itch_net_order_imbalance_indicator_tracking_number_o,
	output logic [6*LEN-1:0] itch_net_order_imbalance_indicator_timestamp_o,
	output logic [8*LEN-1:0] itch_net_order_imbalance_indicator_paired_shares_o,
	output logic [8*LEN-1:0] itch_net_order_imbalance_indicator_imbalance_shares_o,
	output logic [1*LEN-1:0] itch_net_order_imbalance_indicator_imbalance_direction_o,
	output logic [8*LEN-1:0] itch_net_order_imbalance_indicator_stock_o,
	output logic [4*LEN-1:0] itch_net_order_imbalance_indicator_far_price_o,
	output logic [4*LEN-1:0] itch_net_order_imbalance_indicator_near_price_o,
	output logic [4*LEN-1:0] itch_net_order_imbalance_indicator_current_reference_price_o,
	output logic [1*LEN-1:0] itch_net_order_imbalance_indicator_cross_type_o,
	output logic [1*LEN-1:0] itch_net_order_imbalance_indicator_price_variation_indicator_o,
	
	`ifdef GLIMPSE	
	output logic itch_end_of_snapshot_v_o,
	output logic [20*LEN-1:0] itch_end_of_snapshot_sequence_number_o,
	`endif

	output logic itch_retail_price_improvement_indicator_v_o,
	output logic [2*LEN-1:0] itch_retail_price_improvement_indicator_stock_locate_o,
	output logic [2*LEN-1:0] itch_retail_price_improvement_indicator_tracking_number_o,
	output logic [6*LEN-1:0] itch_retail_price_improvement_indicator_timestamp_o,
	output logic [8*LEN-1:0] itch_retail_price_improvement_indicator_stock_o,
	output logic [1*LEN-1:0] itch_retail_price_improvement_indicator_interest_flag_o
);
// data storage
reg   [MSG_MAX_W-1:0]   data_q;
logic [MSG_MAX_W-1:0]   data_next;
logic [CNT_MAX-1:0]     data_en; 
// received counter
reg   [CNT_MAX_W-1:0] data_cnt_q;
logic [CNT_MAX_W-1:0] data_cnt_next;
logic [CNT_MAX_W-1:0] data_cnt_add;
logic                 data_cnt_add_overflow;
logic                 data_cnt_en;
// itch message type
logic [LEN-1:0]       itch_msg_type;
logic                 itch_msg_sent;

// count number of recieved packets
assign { data_cnt_add_overflow, data_cnt_add } = data_cnt_q + { {CNT_MAX_W-1{1'b0}}, valid_i};
// reset to 1 when new msg start, can't set to 0 as we are implicity using
// this counter as a valid signal  
assign data_cnt_next = start_i ? { {CNT_MAX_W-1{1'b0}}, 1'b1 }  : 
					   itch_msg_sent ? {CNT_MAX_W{1'b0}} : data_cnt_add; 

assign data_cnt_en = valid_i | itch_msg_sent;
always @(posedge clk) begin
	if ( ~nreset ) begin
		data_cnt_q <= 1'b0;
	end else if ( data_cnt_en ) begin
		data_cnt_q <= data_cnt_next;
	end
end

genvar i;
generate
	// data_next
	for( i = 0; i < CNT_MAX; i++ ) begin 
		if ( i == CNT_MAX-1) begin
			assign data_next[MSG_MAX_W-1:AXI_DATA_W*i] = data_i[(MSG_MAX_W-AXI_DATA_W*i-1):0];
		end else begin
			assign data_next[AXI_DATA_W*i+AXI_DATA_W-1:AXI_DATA_W*i] = data_i;
		end
	end
	// data_q flop
	always @(posedge clk) begin
		if ( ~nreset ) begin
			data_q[LEN-1:0] <= {LEN{1'b0}};
		end else if ( data_en[0] ) begin
			data_q[AXI_DATA_W-1:0] <= data_next[AXI_DATA_W-1:0];
		end
	end
	for( i = 1; i < CNT_MAX; i++ ) begin
		always @(posedge clk) begin
			if ( data_en[i]) begin
				if ( i == CNT_MAX-1) begin
					data_q[MSG_MAX_W-1:AXI_DATA_W*i] <= data_next[(MSG_MAX_W-AXI_DATA_W*i-1):0]; 
				end else begin
					data_q[AXI_DATA_W*i+AXI_DATA_W-1:AXI_DATA_W*i] <= data_next[AXI_DATA_W*i+AXI_DATA_W-1:AXI_DATA_W*i]; 
				end
			end
		end
	end
	// data_en
	assign data_en[0] = start_i & valid_i;
	for( i = 1; i < CNT_MAX; i++) begin
		assign data_en[i] = (( i + 1 ) == data_cnt_next ) & valid_i;
	end
endgenerate
// message type : allways at offset 0
assign itch_msg_type = data_q[LEN-1:0];
// message has been sent
assign itch_msg_sent = ( itch_system_event_v_o | itch_stock_directory_v_o | itch_stock_trading_action_v_o | 
						 itch_reg_sho_restriction_v_o | itch_market_participant_position_v_o | itch_mwcb_decline_level_v_o |
						 itch_mwcb_status_v_o | itch_ipo_quoting_period_update_v_o | itch_luld_auction_collar_v_o |
						 itch_operational_halt_v_o | itch_add_order_v_o | itch_add_order_with_mpid_v_o | 
					     itch_order_executed_v_o | itch_order_executed_with_price_v_o | itch_order_cancel_v_o |
						 itch_order_delete_v_o | itch_order_replace_v_o | itch_trade_v_o|itch_cross_trade_v_o |
					     itch_broken_trade_v_o | itch_net_order_imbalance_indicator_v_o | 
					     itch_retail_price_improvement_indicator_v_o 
`ifdef GLIMPSE
						 | itch_end_of_snapshot_v_o
`endif
 ); 

// output
// itch message assignement logic
assign itch_system_event_v_o = (itch_msg_type == 'd83) & (data_cnt_q == 'd2);
assign itch_system_event_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_system_event_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_system_event_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_system_event_event_code_o = data_q[LEN*11+LEN*1-1:LEN*11];

assign itch_stock_directory_v_o = (itch_msg_type == 'd82) & (data_cnt_q == 'd5);
assign itch_stock_directory_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_stock_directory_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_stock_directory_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_stock_directory_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_stock_directory_market_category_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_stock_directory_financial_status_indicator_o = data_q[LEN*20+LEN*1-1:LEN*20];
assign itch_stock_directory_round_lot_size_o = data_q[LEN*21+LEN*4-1:LEN*21];
assign itch_stock_directory_round_lots_only_o = data_q[LEN*25+LEN*1-1:LEN*25];
assign itch_stock_directory_issue_classification_o = data_q[LEN*26+LEN*1-1:LEN*26];
assign itch_stock_directory_issue_sub_type_o = data_q[LEN*27+LEN*2-1:LEN*27];
assign itch_stock_directory_authenticity_o = data_q[LEN*29+LEN*1-1:LEN*29];
assign itch_stock_directory_short_sale_threshold_indicator_o = data_q[LEN*30+LEN*1-1:LEN*30];
assign itch_stock_directory_ipo_flag_o = data_q[LEN*31+LEN*1-1:LEN*31];
assign itch_stock_directory_luld_reference_price_tier_o = data_q[LEN*32+LEN*1-1:LEN*32];
assign itch_stock_directory_etp_flag_o = data_q[LEN*33+LEN*1-1:LEN*33];
assign itch_stock_directory_etp_leverage_factor_o = data_q[LEN*34+LEN*4-1:LEN*34];
assign itch_stock_directory_inverse_indicator_o = data_q[LEN*38+LEN*1-1:LEN*38];

assign itch_stock_trading_action_v_o = (itch_msg_type == 'd72) & (data_cnt_q == 'd4);
assign itch_stock_trading_action_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_stock_trading_action_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_stock_trading_action_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_stock_trading_action_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_stock_trading_action_trading_state_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_stock_trading_action_reserved_o = data_q[LEN*20+LEN*1-1:LEN*20];
assign itch_stock_trading_action_reason_o = data_q[LEN*21+LEN*4-1:LEN*21];

assign itch_reg_sho_restriction_v_o = (itch_msg_type == 'd89) & (data_cnt_q == 'd3);
assign itch_reg_sho_restriction_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_reg_sho_restriction_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_reg_sho_restriction_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_reg_sho_restriction_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_reg_sho_restriction_reg_sho_action_o = data_q[LEN*19+LEN*1-1:LEN*19];

assign itch_market_participant_position_v_o = (itch_msg_type == 'd76) & (data_cnt_q == 'd4);
assign itch_market_participant_position_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_market_participant_position_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_market_participant_position_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_market_participant_position_mpid_o = data_q[LEN*11+LEN*4-1:LEN*11];
assign itch_market_participant_position_stock_o = data_q[LEN*15+LEN*8-1:LEN*15];
assign itch_market_participant_position_primary_market_maker_o = data_q[LEN*23+LEN*1-1:LEN*23];
assign itch_market_participant_position_market_maker_mode_o = data_q[LEN*24+LEN*1-1:LEN*24];
assign itch_market_participant_position_market_participant_state_o = data_q[LEN*25+LEN*1-1:LEN*25];

assign itch_mwcb_decline_level_v_o = (itch_msg_type == 'd86) & (data_cnt_q == 'd5);
assign itch_mwcb_decline_level_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_mwcb_decline_level_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_mwcb_decline_level_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_mwcb_decline_level_level_1_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_mwcb_decline_level_level_2_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_mwcb_decline_level_level_3_o = data_q[LEN*27+LEN*8-1:LEN*27];

assign itch_mwcb_status_v_o = (itch_msg_type == 'd87) & (data_cnt_q == 'd2);
assign itch_mwcb_status_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_mwcb_status_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_mwcb_status_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_mwcb_status_breached_level_o = data_q[LEN*11+LEN*1-1:LEN*11];

assign itch_ipo_quoting_period_update_v_o = (itch_msg_type == 'd75) & (data_cnt_q == 'd4);
assign itch_ipo_quoting_period_update_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_ipo_quoting_period_update_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_ipo_quoting_period_update_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_ipo_quoting_period_update_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_ipo_quoting_period_update_ipo_quotation_release_time_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o = data_q[LEN*23+LEN*1-1:LEN*23];
assign itch_ipo_quoting_period_update_ipo_price_o = data_q[LEN*24+LEN*4-1:LEN*24];

assign itch_luld_auction_collar_v_o = (itch_msg_type == 'd74) & (data_cnt_q == 'd5);
assign itch_luld_auction_collar_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_luld_auction_collar_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_luld_auction_collar_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_luld_auction_collar_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_luld_auction_collar_auction_collar_reference_price_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_luld_auction_collar_upper_auction_collar_price_o = data_q[LEN*23+LEN*4-1:LEN*23];
assign itch_luld_auction_collar_lower_auction_collar_price_o = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_luld_auction_collar_auction_collar_extension_o = data_q[LEN*31+LEN*4-1:LEN*31];

assign itch_operational_halt_v_o = (itch_msg_type == 'd104) & (data_cnt_q == 'd3);
assign itch_operational_halt_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_operational_halt_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_operational_halt_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_operational_halt_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_operational_halt_market_code_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_operational_halt_operational_halt_action_o = data_q[LEN*20+LEN*1-1:LEN*20];

assign itch_add_order_v_o = (itch_msg_type == 'd65) & (data_cnt_q == 'd5);
assign itch_add_order_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_add_order_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_add_order_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_add_order_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_add_order_buy_sell_indicator_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_add_order_shares_o = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_add_order_stock_o = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_add_order_price_o = data_q[LEN*32+LEN*4-1:LEN*32];

assign itch_add_order_with_mpid_v_o = (itch_msg_type == 'd70) & (data_cnt_q == 'd5);
assign itch_add_order_with_mpid_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_add_order_with_mpid_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_add_order_with_mpid_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_add_order_with_mpid_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_add_order_with_mpid_buy_sell_indicator_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_add_order_with_mpid_shares_o = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_add_order_with_mpid_stock_o = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_add_order_with_mpid_price_o = data_q[LEN*32+LEN*4-1:LEN*32];
assign itch_add_order_with_mpid_attribution_o = data_q[LEN*36+LEN*4-1:LEN*36];

assign itch_order_executed_v_o = (itch_msg_type == 'd69) & (data_cnt_q == 'd4);
assign itch_order_executed_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_executed_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_executed_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_executed_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_executed_executed_shares_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_order_executed_match_number_o = data_q[LEN*23+LEN*8-1:LEN*23];

assign itch_order_executed_with_price_v_o = (itch_msg_type == 'd67) & (data_cnt_q == 'd5);
assign itch_order_executed_with_price_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_executed_with_price_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_executed_with_price_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_executed_with_price_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_executed_with_price_executed_shares_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_order_executed_with_price_match_number_o = data_q[LEN*23+LEN*8-1:LEN*23];
assign itch_order_executed_with_price_printable_o = data_q[LEN*31+LEN*1-1:LEN*31];
assign itch_order_executed_with_price_execution_price_o = data_q[LEN*32+LEN*4-1:LEN*32];

assign itch_order_cancel_v_o = (itch_msg_type == 'd88) & (data_cnt_q == 'd3);
assign itch_order_cancel_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_cancel_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_cancel_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_cancel_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_cancel_cancelled_shares_o = data_q[LEN*19+LEN*4-1:LEN*19];

assign itch_order_delete_v_o = (itch_msg_type == 'd68) & (data_cnt_q == 'd3);
assign itch_order_delete_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_delete_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_delete_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_delete_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];

assign itch_order_replace_v_o = (itch_msg_type == 'd85) & (data_cnt_q == 'd5);
assign itch_order_replace_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_replace_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_replace_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_replace_original_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_replace_new_order_reference_number_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_order_replace_shares_o = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_order_replace_price_o = data_q[LEN*31+LEN*4-1:LEN*31];

assign itch_trade_v_o = (itch_msg_type == 'd80) & (data_cnt_q == 'd6);
assign itch_trade_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_trade_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_trade_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_trade_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_trade_buy_sell_indicator_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_trade_shares_o = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_trade_stock_o = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_trade_price_o = data_q[LEN*32+LEN*4-1:LEN*32];
assign itch_trade_match_number_o = data_q[LEN*36+LEN*8-1:LEN*36];

assign itch_cross_trade_v_o = (itch_msg_type == 'd81) & (data_cnt_q == 'd5);
assign itch_cross_trade_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_cross_trade_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_cross_trade_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_cross_trade_shares_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_cross_trade_stock_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_cross_trade_cross_price_o = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_cross_trade_match_number_o = data_q[LEN*31+LEN*8-1:LEN*31];
assign itch_cross_trade_cross_type_o = data_q[LEN*39+LEN*1-1:LEN*39];

assign itch_broken_trade_v_o = (itch_msg_type == 'd66) & (data_cnt_q == 'd3);
assign itch_broken_trade_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_broken_trade_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_broken_trade_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_broken_trade_match_number_o = data_q[LEN*11+LEN*8-1:LEN*11];

assign itch_net_order_imbalance_indicator_v_o = (itch_msg_type == 'd73) & (data_cnt_q == 'd7);
assign itch_net_order_imbalance_indicator_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_net_order_imbalance_indicator_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_net_order_imbalance_indicator_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_net_order_imbalance_indicator_paired_shares_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_net_order_imbalance_indicator_imbalance_shares_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_net_order_imbalance_indicator_imbalance_direction_o = data_q[LEN*27+LEN*1-1:LEN*27];
assign itch_net_order_imbalance_indicator_stock_o = data_q[LEN*28+LEN*8-1:LEN*28];
assign itch_net_order_imbalance_indicator_far_price_o = data_q[LEN*36+LEN*4-1:LEN*36];
assign itch_net_order_imbalance_indicator_near_price_o = data_q[LEN*40+LEN*4-1:LEN*40];
assign itch_net_order_imbalance_indicator_current_reference_price_o = data_q[LEN*44+LEN*4-1:LEN*44];
assign itch_net_order_imbalance_indicator_cross_type_o = data_q[LEN*48+LEN*1-1:LEN*48];
assign itch_net_order_imbalance_indicator_price_variation_indicator_o = data_q[LEN*49+LEN*1-1:LEN*49];

assign itch_retail_price_improvement_indicator_v_o = (itch_msg_type == 'd78) & (data_cnt_q == 'd3);
assign itch_retail_price_improvement_indicator_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_retail_price_improvement_indicator_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_retail_price_improvement_indicator_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_retail_price_improvement_indicator_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_retail_price_improvement_indicator_interest_flag_o = data_q[LEN*19+LEN*1-1:LEN*19];

`ifdef GLIMPSE
assign itch_end_of_snapshot_v_o = (itch_msg_type == 'd71) & (data_cnt_q == 'd3);
assign itch_end_of_snapshot_sequence_number_o = data_q[(LEN*1+LEN*20)-1:LEN*1];
`endif
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
		for(int unsigned x = 0; x < CNT_MAX; x++ ) begin 
			// assert( ~(data_cnt_q == x) | ( (data_cnt_q == x ) & ~$isunknown( data_q[AXI_DATA_W*x+AXI_DATA_W-1:AXI_DATA_W*x])));
		end

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
