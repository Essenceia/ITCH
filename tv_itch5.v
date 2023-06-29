/* Copyright (c) 2023, Julia Desmazes. All rights reserved.
 * 
 * This work is licensed under the Creative Commons Attribution-NonCommercial
 * 4.0 International License. 
 * 
 * This code is provided "as is" without any express or implied warranties. */ 

// Top module, dispatches streams to multiple decoders
module tv_itch5 #(
	`ifdef DEBUG_ID
	parameter DEBUG_ID_W = 64,
	`endif
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = AXI_DATA_W / 8,
	parameter KEEP_LW    = $clog2(AXI_KEEP_W) + 1,
	
	// number of decoders
	parameter ITCH_N = 2,

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
	input [ITCH_N-1:0]            valid_i,
	input [ITCH_N-1:0]            start_i,
	input [ITCH_N*KEEP_LW-1:0]    len_i,
	input [ITCH_N*AXI_DATA_W-1:0] data_i
	
);
// itch interface
tv_itch5_if  itch_o[ITCH_N-1:0]();
// muxed version of itch decoders output
tv_itch5_if itch_mux_o();
`ifdef EARLY
tv_itch5_early_if  early_o[ITCH_N-1:0]();
`endif

// Instanciate multiple itch decoders
genvar i;
generate
	for( i=0; i<ITCH_N; i++) begin
		tv_itch5_dec
		m_tv_itch5_dec(
			.clk   (clk   ),
			.nreset(nreset),
		
			`ifdef DEBUG_ID
			.debug_id_i(debug_id_i),    
			.debug_id_o(debug_id_o),
			`endif
		
			.valid_i(valid_i[i]),
			.start_i(start_i[i]),
			.data_i (data_i[i*AXI_DATA_W+AXI_DATA_W-1:i*AXI_DATA_W]),
			.len_i  (len_i[i*KEEP_LW+KEEP_LW-1:i*KEEP_LW])
		);
		always_comb begin
			itch_mux_o <= m_tv_itch5_dec.itch_o;
		`ifdef EARLY
		assign early_o[i] = m_tv_itch5_dec.early_o;
		`endif
		end
	end
endgenerate
endmodule
