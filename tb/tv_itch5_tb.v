/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

module tv_itch5_tb;

reg clk    = 0;
reg nreset = 1'b0;	

localparam LEN = 8;
localparam AXI_DATA_W = 64;
localparam AXI_KEEP_W = AXI_DATA_W / 8;
localparam KEEP_LW    = $clog2(AXI_KEEP_W) + 1;

// overlap fields
localparam OV_DATA_W  = 64-(2*LEN);//48
localparam OV_KEEP_W  = (OV_DATA_W/8);//6
localparam OV_KEEP_LW = 3;//$clog2(OV_KEEP_W+1),	


localparam DEBUG_ID_W = 64;

logic                  valid_i = 1'b0;
logic                  start_i;
logic [KEEP_LW-1:0]    len_i;
logic [AXI_DATA_W-1:0] data_i;

logic                  ov_valid_i = 1'b0;
logic [OV_KEEP_LW-1:0] ov_len_i;
logic [OV_DATA_W-1:0]  ov_data_i;


`ifdef DEBUG_ID
logic [DEBUG_ID_W-1:0] debug_id_i;
logic [DEBUG_ID_W-1:0] debug_id_o;
`endif

`include "gen/tb_sig_list.v"

`ifdef DEBUG_ID
logic [DEBUG_ID_W-1:0] tb_debug_id;
`endif

logic [20*LEN-1:0] tb_eos_data;
logic [LEN-1:0]    tb_msg_type;

always #5 clk = ~clk;

initial begin
	$dumpfile("build/wave.vcd");
	$dumpvars(0, tv_itch5_tb);
	`ifdef DEBUG
	$display("Debug activated : Starting test");
	`endif
	// reset
	#10
	nreset = 1'b1;
	// start test
	#10
	valid_i = 1'b1;
	start_i = 1'b1;

	`ifdef DEBUG_ID
	tb_debug_id = { $random(), $random()};
	debug_id_i  = tb_debug_id;
	`endif

	// send simple end of snapshot msg, len = 21 bytes
	// will be sent over the next 3 cycles
	tb_msg_type  = "G"; 
	tb_eos_data  = {  5{32'hFFFFFFFF}};
	data_i       = { tb_eos_data[AXI_DATA_W-LEN-1:0], tb_msg_type };
	len_i        = 'd8;

	#10

	// eos msg part 2/3
	start_i = 1'b0;
	data_i  = tb_eos_data[AXI_DATA_W*2-LEN-1:AXI_DATA_W-LEN];
	
	#10
	
	// eos msg part 3/3 + overlap with start of new mold msg of type add order

	data_i  = { {AXI_DATA_W*3-LEN*21-1{1'bx}} , tb_eos_data[LEN*20-1:AXI_DATA_W*2-LEN] };
	len_i = 'd5;
 	// overlap
	ov_valid_i = 1'b1;
	tb_msg_type = "A";
	ov_data_i = { 'x , tb_msg_type};
	ov_len_i = 'd1;

	#10

	// add order 2/6
	ov_valid_i = 1'b0;
	ov_len_i = 'x;
	data_i =  {8{8'haa}};
	len_i = 'd8;

	#5
	`ifdef GLIMPSE
	$display("Testing glimpse decode");
	assert( itch_end_of_snapshot_v_o );
	assert( itch_end_of_snapshot_sequence_number_o == tb_eos_data );
	`else
	// glimpse not supported, no message should have been seen
	assert( ~m_uut.itch_msg_sent );
	`endif // GLIMPSE
	#5
	
	// add order 3/6
	data_i =  {8{8'hbb}};

	#10


	// add order 4/6
    data_i =  {8{8'hcc}};

	#10

	// add order 5/6
	data_i =  {8{8'hdd}};

	#10

	// add order 6/6
	data_i = { 'x, {3{8'hee}}};
	len_i = 'd3;

	#10

	valid_i = 1'b0;
	data_i = 'x;

	// check results
`ifdef DEBUG_ID
	assert( debug_id_o == tb_debug_id );
`endif
	#20
	`ifdef DEBUG
	$display("Test end");
	`endif
	$finish;
end

tv_itch5 #( .LEN(LEN))
m_uut(
	.clk(clk),
	.nreset(nreset),

	.valid_i(valid_i),
	.start_i(start_i),
	.len_i  (len_i),
	.data_i (data_i),

	.ov_valid_i(ov_valid_i),
	.ov_len_i  (ov_len_i),
	.ov_data_i (ov_data_i),


	`ifdef DEBUG_ID
	.debug_id_i(debug_id_i),    
	.debug_id_o(debug_id_o),
	`endif
	`include "gen/tb_port_list.v"
);
endmodule

