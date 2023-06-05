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

	parameter MSG_MAX_W = 50*LEN,// maximum length an itch message
	parameter CNT_MAX = 7,// $ceil(MSG_MAX_W / AXI_DATA_W) // maxium number of payloads that need to be received for the longest itch message 
	parameter CNT_MAX_W = $clog2(CNT_MAX),
	parameter MAX_W   = CNT_MAX*AXI_DATA_W, 

	parameter TYPE_W = LEN, // message type
	parameter STOCK_W = LEN*8, // stock symbole
	parameter U32_W = LEN*4,
	parameter LOC_W = LEN*2, // stock location
	parameter PRICE4_W = LEN*4,
	parameter TIME_W = LEN*6,// timestamp

)(
	input clk,
	input nreset,

	//moldupd64
	input mold_v_i,
	input mold_start_i,
	input [AXI_DATA_W-1:0] mold_data_i,

	`ifdef MOLD_MSD_IDS
	input [SID_W-1:0]     mold_sid_i,
	input [SEQ_NUM_W-1:0] mold_seq_num_i, 
	`endif 

	
	
);
// data storage
reg   [MAX_W-1:0]   data_q;
logic [MAX_W-1:0]   data_next;
logic [CNT_MAX-1:0] data_en; 
// received counter
reg   [CNT_MAX_W-1:0] data_cnt_q;
logic [CNT_MAX_W-1:0] data_cnt_next;
logic [CNT_MAX_W-1:0] data_cnt_add;
logic                 data_cnt_add_overflow;
logic                 data_cnt_en;


// count number of recieved packets
assign { data_cnt_add_overflow, data_cnt_add } = data_cnt_q + { {CNT_MAX_W-1{1'b0}}, mold_v_i};
// reset to 1 when new msg start, can't set to 0 as we are implicity using
// this counter as a valid signal  
assign data_cnt_next = mold_start_i ? { {CNT_MAX_W-1{1'b0}}, 1'b1 }  : data_cnt_add; 

assign data_cnt_en = mold_v_i;
always @(posedge clk) begin
	if ( nreset ) begin
		data_cnt_q <= 1'b0;
	end else begin
		data_cnt_q <= data_cnt_next;
	end
end

// data
genvar i;
generate
	for( i = 0; i < CNT_MAX; i++ ) begin
		assign data_next[AXI_DATA_W*i+AXI_DATA_W-1:AXI_KEEP_W*i] = mold_data_i;
		always @(posedge clk) begin
			if ( data_en[i]) begin
				data_q[AXI_DATA_W*i+AXI_DATA_W-1:AXI_DATA_W*i] <= data_next[AXI_DATA_W*i+AXI_DATA_W-1:AXI_DATA_W*i]; 
			end
		end
	end
	assign data_en[0] = mold_start_i & mold_v_i;
	for( i = 1; i < CNT_MAX; i++) begin
		assign data_en[i] = (( i - 1 ) == data_cnt_q ) & mold_v_i;
	end
endgenerate
 
`ifdef FORMAL
initial begin
	a_reset : assume( ~nreset);
end

always @(posedge clk) begin
	if ( nreset ) begin
		// should never receive more than the max expected number of packets
		a_data_cnt_overflow : assume ( ~data_cnt_add_overflow );

		// xcheck
		sva_xcheck_data_cnt : assert ( ~$isunknown( data_cnt_q ));
		for(int unsigned x = 0; x < CNT_MAX; x++ ) begin 
			 assert( ~(data_cnt_q == x) | ( (data_cnt_q == x ) & ~$isunknown( data_q[AXI_DATA_W*x+AXI_DATA_W-1:AXI_DATA_W*x])));
		end
	end
end

`endif
endmodule
