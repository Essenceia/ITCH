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
	// itch data
	parameter LEN = 8,

	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = AXI_DATA_W / 8,
	parameter KEEP_LW    = $clog2(AXI_KEEP_W) + 1,

	// overlap fields
	parameter OV_DATA_W  = 64-(2*LEN),//48
	parameter OV_KEEP_W  = (OV_DATA_W/8),//6
	parameter OV_KEEP_LW = 3, //$clog2(OV_KEEP_W+1),	

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
	input [AXI_DATA_W-1:0] data_i,
	// overlap message bits, only valid for first payload
	input                  ov_valid_i,
	input [OV_KEEP_LW-1:0] ov_len_i,
	input [OV_DATA_W-1:0]  ov_data_i,

	`ifdef EARLY
	`include "gen/early_port_list.v"
	`endif // EARLY

	`include "gen/port_list.v"	
);
localparam OV_KEEP_LW_DIFF = KEEP_LW > OV_KEEP_LW ? KEEP_LW-OV_KEEP_LW : 0;
// received byte counter
reg   [MSG_MAX_W-1:0]  data_cnt_q;
logic [MSG_MAX_W-1:0]  data_cnt_next;
logic [MSG_MAX_W-1:0]  data_cnt_add;
logic                  data_cnt_add_overflow;
logic                  data_cnt_en;

// overlap ( delay data by 1 cycle ) 
logic                  ov_v_next;
reg                    ov_v_q;
logic [OV_KEEP_LW-1:0] ov_len_next;
reg   [OV_KEEP_LW-1:0] ov_len_q;
logic [OV_DATA_W-1:0]  ov_data_next;
reg   [OV_DATA_W-1:0]  ov_data_q;
logic [KEEP_LW-2:0]    ov_data_cnt_add;
logic                  ov_data_cnt_add_overflow;


// itch message type
logic [LEN-1:0]        itch_msg_type;
logic                  itch_msg_sent;
`ifdef DEBUG_ID
reg   [DEBUG_ID_W-1:0] debug_id_q;
logic [DEBUG_ID_W-1:0] debug_id_next;
logic                  debug_id_en;
`endif
reg                    valid_q;
always @(posedge clk) begin
	valid_q <= valid_i;
end

// overlap logic : delay writing to data by 1 cycle
assign ov_v_next    = ov_valid_i;
assign ov_len_next  = ov_len_i;
assign ov_data_next = ov_data_i;
always @(posedge clk) begin
	if ( ~nreset ) begin
		ov_v_q <= 1'b0;
	end else begin
		ov_v_q <= ov_v_next;
		ov_len_q <= ov_len_next;
		ov_data_q <= ov_data_next;
	end
end
 
// count number of recieved bytes
assign { data_cnt_add_overflow, data_cnt_add } = data_cnt_q + { {MSG_MAX_W-KEEP_LW{1'b0}}, len_i};
assign { ov_data_cnt_add_overflow, ov_data_cnt_add} = {{OV_KEEP_LW_DIFF{1'b0}} , ov_len_q} + len_i;
// reset to 1 when new msg start, can't set to 0 as we are implicity using
// this counter as a valid signal 

assign data_cnt_next =  { KEEP_LW{ start_i}} &  len_i 
					  | { KEEP_LW{ ov_v_q }} & { ov_data_cnt_add_overflow, ov_data_cnt_add }
					  | { MSG_MAX_W{ ~start_i & ~ov_v_q}} & data_cnt_add; 

assign data_cnt_en = valid_i | valid_q;
always @(posedge clk) begin
	if ( ~nreset ) begin
		data_cnt_q <= 1'b0;
	end else if ( data_cnt_en ) begin
		data_cnt_q <= data_cnt_next;
	end
end
// convert input length to data mask
logic [AXI_KEEP_W-1:0] data_mask_lite;
logic [AXI_DATA_W-1:0] data_mask;
len_to_mask #(.LEN_W(KEEP_LW), .LEN_MAX(AXI_KEEP_W) )
m_itch_len_to_mask(
	.len_i(len_i),
	.mask_o(data_mask_lite)
);
genvar i;
generate
	for(i=0; i<AXI_KEEP_W;i++) begin
		assign data_mask[i*LEN+LEN-1:i*LEN] = {LEN{data_mask_lite[i]}};
	end
endgenerate


// overflow mask
logic [OV_KEEP_LW-1:0]    ov_len;
logic [OV_KEEP_W-1:0  ]   ov_data_mask_lite;
logic [OV_KEEP_W*LEN-1:0] ov_data_mask;

assign ov_len = ov_len_q & { OV_KEEP_LW{ ov_v_q }};
len_to_mask #(.LEN_W(OV_KEEP_LW), .LEN_MAX(OV_KEEP_W) )
m_itch_ov_len_to_mask(
	.len_i(ov_len ),
	.mask_o(ov_data_mask_lite)
);
generate
	for(i=0; i<OV_KEEP_W;i++) begin
		assign ov_data_mask[i*LEN+LEN-1:i*LEN] = {LEN{ ov_data_mask_lite[i]}};
	end
endgenerate

// shift received bytes into the correct position
// data_shifted unused bits are writen to x
localparam OFF_W = $clog2(AXI_DATA_W/AXI_KEEP_W);
logic [OFF_W-1:0]        data_off;
logic [2*AXI_DATA_W-1:0] data_mask_shifted_arr[AXI_KEEP_W-1:0];
logic [2*AXI_DATA_W-1:0] data_shifted_arr[AXI_KEEP_W-1:0];
logic [2*AXI_DATA_W-1:0] data_mask_shifted;
logic [2*AXI_DATA_W-1:0] data_shifted;


assign data_off = { OFF_W{start_i}} & 'd0 
				| { OFF_W{ov_v_q }} &  ov_len_q[OFF_W-1:0]
				| { OFF_W{~start_i&~ov_v_q}} & data_cnt_q[OFF_W-1:0]; 
generate
	for(i=0; i<AXI_KEEP_W; i++)begin
		assign data_mask_shifted_arr[i] = { {AXI_DATA_W-i*LEN{1'b0}}, data_mask,{i*LEN{1'b0}}};
		assign data_shifted_arr[i]      = { {AXI_DATA_W-i*LEN{1'bx}}, data_i,   {i*LEN{1'bx}}};
	end
endgenerate
always_comb begin
	for(int j=0; j<AXI_KEEP_W; j++)begin
		if( data_off == j ) data_mask_shifted = data_mask_shifted_arr[j];
		if( data_off == j ) data_shifted      = data_shifted_arr[j];
	end
end

// write select bytes by groups of 8
// data storage
localparam LEN_W = $clog2(LEN);

reg   [MSG_MAX_N-1:0] data_q;
logic [MSG_MAX_N-1:0] data_next;
logic [PL_MAX_N-1:0]  data_en; 
logic [PL_MAX_N-1:0]  data_start_en;  /* synthesis keep */  
logic [PL_MAX_N-1:0]  data_end_en;/* synthesis keep */ 
logic [MSG_MAX_W-1:0] cnt_end;
logic                 cnt_end_offset;
logic                 data_overlap; // overlap on 8 byte data boundary

logic [PL_MAX_N*AXI_DATA_W-1:MSG_MAX_N] data_next_unused;
logic [AXI_DATA_W-1:0] data_lsb;
logic [AXI_DATA_W-1:0] data_msb;

assign data_overlap = |data_cnt_next[LEN_W-1:0]; 
generate	
	assign data_start_en[0] = start_i | ov_v_q | ~|data_cnt_q[MSG_MAX_W-1:LEN_W];  
	assign data_end_en[0]   = 1'b0; // not used
	assign data_en[0]       = data_start_en[0]  & valid_i;
	for(i=1; i<PL_MAX_N; i++) begin
		// enable
		if ( i == 1 ) begin
			assign data_start_en[1] = ( ov_v_q & ov_data_cnt_add_overflow )
								    | ( data_cnt_q[MSG_MAX_W-1:LEN_W] == i ); 
		end else begin
			assign data_start_en[i] = ( data_cnt_q[MSG_MAX_W-1:LEN_W] == i ) & ~( start_i | ov_v_q ); 
		end
		if ( i == 2 ) begin
			assign data_end_en[i]   = ( data_start_en[1] & data_overlap  ) &  ~ov_v_q;
		end else begin
			assign data_end_en[i]   = ( data_start_en[i-1] & data_overlap  );
		end	
		assign data_en[i] = ( data_start_en[i] | data_end_en[i] ) & valid_i;
	end

	// first payload
	logic [AXI_DATA_W-1:0] data_mask_flopped_lsb;
	assign data_mask_flopped_lsb = ~{ data_mask_shifted[AXI_DATA_W-1:OV_DATA_W], ov_data_mask | data_mask_shifted[OV_DATA_W-1:0] };
	
	assign data_next[AXI_DATA_W-1:0] = data_mask_flopped_lsb & data_q[AXI_DATA_W-1:0]
									 | data_lsb 
									 | {{AXI_DATA_W-OV_DATA_W{1'b0}}, ov_data_mask & ov_data_q} ;
	always @(posedge clk) begin
		if(data_en[0]) begin
				data_q[AXI_DATA_W-1:0] <= data_next[AXI_DATA_W-1:0]; 
		end
	end
	assign data_lsb = data_shifted[AXI_DATA_W-1:0] & data_mask_shifted[AXI_DATA_W-1:0];
	assign data_msb = data_shifted[2*AXI_DATA_W-1:AXI_DATA_W] & data_mask_shifted[2*AXI_DATA_W-1:AXI_DATA_W];

	for(i=1; i<PL_MAX_N; i++) begin
		if ( i == PL_MAX_N -1 ) begin
			assign { data_next_unused, data_next[MSG_MAX_N-1:i*AXI_DATA_W] } =	data_end_en[i] ?
			  ( data_q[MSG_MAX_N-1:i*AXI_DATA_W]        & ~data_mask_shifted[2*AXI_DATA_W-1:AXI_DATA_W] ) 
			 |( data_shifted[2*AXI_DATA_W-1:AXI_DATA_W] &  data_mask_shifted[2*AXI_DATA_W-1:AXI_DATA_W] )
			 :( data_q[MSG_MAX_N-1:i*AXI_DATA_W]        & ~data_mask_shifted[AXI_DATA_W-1:0] ) 
			 |( data_shifted[AXI_DATA_W-1:0]            &  data_mask_shifted[AXI_DATA_W-1:0] );
			always @(posedge clk) begin
				if(data_en[PL_MAX_N-1]) begin
					data_q[MSG_MAX_N-1:i*AXI_DATA_W] <= data_next[MSG_MAX_N-1:i*AXI_DATA_W]; 
				end
			end
		end else begin
			assign data_next[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W] = data_end_en[i] ? 
			        ( data_q[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W] & ~data_mask_shifted[2*AXI_DATA_W-1:AXI_DATA_W] ) | data_msb
			       :( data_q[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W] & ~data_mask_shifted[AXI_DATA_W-1:0]            ) | data_lsb;
		//		data_shifted[2*AXI_DATA_W-1:AXI_DATA_W] : data_shifted[AXI_DATA_W-1:0];
			always @(posedge clk) begin
				if(data_en[i]) begin
					data_q[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W] <= data_next[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W]; 
				end
			end
		end
	end
endgenerate

`include "gen/assign_logic.v"

`ifdef EARLY
`include "gen/assign_early_logic.v"
`endif // EARLY

`ifdef DEBUG_ID
// debug id
assign debug_id_next = debug_id_i;
assign debug_id_en   = valid_i & ( start_i | ov_v_q ) ;
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
assign itch_msg_sent = ( 
					   itch_system_event_v_o 
					 | itch_stock_directory_v_o
					 | itch_stock_trading_action_v_o 
					 | itch_reg_sho_restriction_v_o
					 | itch_market_participant_position_v_o
					 | itch_mwcb_decline_level_v_o
					 | itch_mwcb_status_v_o
					 | itch_ipo_quoting_period_update_v_o
					 | itch_luld_auction_collar_v_o
					 | itch_operational_halt_v_o
					 | itch_add_order_v_o
					 | itch_add_order_with_mpid_v_o
					 | itch_order_executed_v_o
					 | itch_order_executed_with_price_v_o
					 | itch_order_cancel_v_o
					 | itch_order_delete_v_o
					 | itch_order_replace_v_o
					 | itch_trade_v_o
					 | itch_cross_trade_v_o
					 | itch_broken_trade_v_o
					 | itch_net_order_imbalance_indicator_v_o
					 | itch_retail_price_improvement_indicator_v_o 
`ifdef GLIMPSE
					 | itch_end_of_snapshot_v_o
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
		`include "gen/formal.v"	
	end
end

`endif
endmodule
