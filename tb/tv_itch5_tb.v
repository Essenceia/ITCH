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

logic itch_system_event_v_o;
logic [2*LEN-1:0] itch_system_event_stock_locate_o;
logic [2*LEN-1:0] itch_system_event_tracking_number_o;
logic [6*LEN-1:0] itch_system_event_timestamp_o;
logic [1*LEN-1:0] itch_system_event_event_code_o;

logic itch_stock_directory_v_o;
logic [2*LEN-1:0] itch_stock_directory_stock_locate_o;
logic [2*LEN-1:0] itch_stock_directory_tracking_number_o;
logic [6*LEN-1:0] itch_stock_directory_timestamp_o;
logic [8*LEN-1:0] itch_stock_directory_stock_o;
logic [1*LEN-1:0] itch_stock_directory_market_category_o;
logic [1*LEN-1:0] itch_stock_directory_financial_status_indicator_o;
logic [4*LEN-1:0] itch_stock_directory_round_lot_size_o;
logic [1*LEN-1:0] itch_stock_directory_round_lots_only_o;
logic [1*LEN-1:0] itch_stock_directory_issue_classification_o;
logic [2*LEN-1:0] itch_stock_directory_issue_sub_type_o;
logic [1*LEN-1:0] itch_stock_directory_authenticity_o;
logic [1*LEN-1:0] itch_stock_directory_short_sale_threshold_indicator_o;
logic [1*LEN-1:0] itch_stock_directory_ipo_flag_o;
logic [1*LEN-1:0] itch_stock_directory_luld_reference_price_tier_o;
logic [1*LEN-1:0] itch_stock_directory_etp_flag_o;
logic [4*LEN-1:0] itch_stock_directory_etp_leverage_factor_o;
logic [1*LEN-1:0] itch_stock_directory_inverse_indicator_o;

logic itch_stock_trading_action_v_o;
logic [2*LEN-1:0] itch_stock_trading_action_stock_locate_o;
logic [2*LEN-1:0] itch_stock_trading_action_tracking_number_o;
logic [6*LEN-1:0] itch_stock_trading_action_timestamp_o;
logic [8*LEN-1:0] itch_stock_trading_action_stock_o;
logic [1*LEN-1:0] itch_stock_trading_action_trading_state_o;
logic [1*LEN-1:0] itch_stock_trading_action_reserved_o;
logic [4*LEN-1:0] itch_stock_trading_action_reason_o;

logic itch_reg_sho_restriction_v_o;
logic [2*LEN-1:0] itch_reg_sho_restriction_stock_locate_o;
logic [2*LEN-1:0] itch_reg_sho_restriction_tracking_number_o;
logic [6*LEN-1:0] itch_reg_sho_restriction_timestamp_o;
logic [8*LEN-1:0] itch_reg_sho_restriction_stock_o;
logic [1*LEN-1:0] itch_reg_sho_restriction_reg_sho_action_o;

logic itch_market_participant_position_v_o;
logic [2*LEN-1:0] itch_market_participant_position_stock_locate_o;
logic [2*LEN-1:0] itch_market_participant_position_tracking_number_o;
logic [6*LEN-1:0] itch_market_participant_position_timestamp_o;
logic [4*LEN-1:0] itch_market_participant_position_mpid_o;
logic [8*LEN-1:0] itch_market_participant_position_stock_o;
logic [1*LEN-1:0] itch_market_participant_position_primary_market_maker_o;
logic [1*LEN-1:0] itch_market_participant_position_market_maker_mode_o;
logic [1*LEN-1:0] itch_market_participant_position_market_participant_state_o;

logic itch_mwcb_decline_level_v_o;
logic [2*LEN-1:0] itch_mwcb_decline_level_stock_locate_o;
logic [2*LEN-1:0] itch_mwcb_decline_level_tracking_number_o;
logic [6*LEN-1:0] itch_mwcb_decline_level_timestamp_o;
logic [8*LEN-1:0] itch_mwcb_decline_level_level_1_o;
logic [8*LEN-1:0] itch_mwcb_decline_level_level_2_o;
logic [8*LEN-1:0] itch_mwcb_decline_level_level_3_o;

logic itch_mwcb_status_v_o;
logic [2*LEN-1:0] itch_mwcb_status_stock_locate_o;
logic [2*LEN-1:0] itch_mwcb_status_tracking_number_o;
logic [6*LEN-1:0] itch_mwcb_status_timestamp_o;
logic [1*LEN-1:0] itch_mwcb_status_breached_level_o;

logic itch_ipo_quoting_period_update_v_o;
logic [2*LEN-1:0] itch_ipo_quoting_period_update_stock_locate_o;
logic [2*LEN-1:0] itch_ipo_quoting_period_update_tracking_number_o;
logic [6*LEN-1:0] itch_ipo_quoting_period_update_timestamp_o;
logic [8*LEN-1:0] itch_ipo_quoting_period_update_stock_o;
logic [4*LEN-1:0] itch_ipo_quoting_period_update_ipo_quotation_release_time_o;
logic [1*LEN-1:0] itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o;
logic [4*LEN-1:0] itch_ipo_quoting_period_update_ipo_price_o;

logic itch_luld_auction_collar_v_o;
logic [2*LEN-1:0] itch_luld_auction_collar_stock_locate_o;
logic [2*LEN-1:0] itch_luld_auction_collar_tracking_number_o;
logic [6*LEN-1:0] itch_luld_auction_collar_timestamp_o;
logic [8*LEN-1:0] itch_luld_auction_collar_stock_o;
logic [4*LEN-1:0] itch_luld_auction_collar_auction_collar_reference_price_o;
logic [4*LEN-1:0] itch_luld_auction_collar_upper_auction_collar_price_o;
logic [4*LEN-1:0] itch_luld_auction_collar_lower_auction_collar_price_o;
logic [4*LEN-1:0] itch_luld_auction_collar_auction_collar_extension_o;

logic itch_operational_halt_v_o;
logic [2*LEN-1:0] itch_operational_halt_stock_locate_o;
logic [2*LEN-1:0] itch_operational_halt_tracking_number_o;
logic [6*LEN-1:0] itch_operational_halt_timestamp_o;
logic [8*LEN-1:0] itch_operational_halt_stock_o;
logic [1*LEN-1:0] itch_operational_halt_market_code_o;
logic [1*LEN-1:0] itch_operational_halt_operational_halt_action_o;

logic itch_add_order_v_o;
logic [2*LEN-1:0] itch_add_order_stock_locate_o;
logic [2*LEN-1:0] itch_add_order_tracking_number_o;
logic [6*LEN-1:0] itch_add_order_timestamp_o;
logic [8*LEN-1:0] itch_add_order_order_reference_number_o;
logic [1*LEN-1:0] itch_add_order_buy_sell_indicator_o;
logic [4*LEN-1:0] itch_add_order_shares_o;
logic [8*LEN-1:0] itch_add_order_stock_o;
logic [4*LEN-1:0] itch_add_order_price_o;

logic itch_add_order_with_mpid_v_o;
logic [2*LEN-1:0] itch_add_order_with_mpid_stock_locate_o;
logic [2*LEN-1:0] itch_add_order_with_mpid_tracking_number_o;
logic [6*LEN-1:0] itch_add_order_with_mpid_timestamp_o;
logic [8*LEN-1:0] itch_add_order_with_mpid_order_reference_number_o;
logic [1*LEN-1:0] itch_add_order_with_mpid_buy_sell_indicator_o;
logic [4*LEN-1:0] itch_add_order_with_mpid_shares_o;
logic [8*LEN-1:0] itch_add_order_with_mpid_stock_o;
logic [4*LEN-1:0] itch_add_order_with_mpid_price_o;
logic [4*LEN-1:0] itch_add_order_with_mpid_attribution_o;

logic itch_order_executed_v_o;
logic [2*LEN-1:0] itch_order_executed_stock_locate_o;
logic [2*LEN-1:0] itch_order_executed_tracking_number_o;
logic [6*LEN-1:0] itch_order_executed_timestamp_o;
logic [8*LEN-1:0] itch_order_executed_order_reference_number_o;
logic [4*LEN-1:0] itch_order_executed_executed_shares_o;
logic [8*LEN-1:0] itch_order_executed_match_number_o;

logic itch_order_executed_with_price_v_o;
logic [2*LEN-1:0] itch_order_executed_with_price_stock_locate_o;
logic [2*LEN-1:0] itch_order_executed_with_price_tracking_number_o;
logic [6*LEN-1:0] itch_order_executed_with_price_timestamp_o;
logic [8*LEN-1:0] itch_order_executed_with_price_order_reference_number_o;
logic [4*LEN-1:0] itch_order_executed_with_price_executed_shares_o;
logic [8*LEN-1:0] itch_order_executed_with_price_match_number_o;
logic [1*LEN-1:0] itch_order_executed_with_price_printable_o;
logic [4*LEN-1:0] itch_order_executed_with_price_execution_price_o;

logic itch_order_cancel_v_o;
logic [2*LEN-1:0] itch_order_cancel_stock_locate_o;
logic [2*LEN-1:0] itch_order_cancel_tracking_number_o;
logic [6*LEN-1:0] itch_order_cancel_timestamp_o;
logic [8*LEN-1:0] itch_order_cancel_order_reference_number_o;
logic [4*LEN-1:0] itch_order_cancel_cancelled_shares_o;

logic itch_order_delete_v_o;
logic [2*LEN-1:0] itch_order_delete_stock_locate_o;
logic [2*LEN-1:0] itch_order_delete_tracking_number_o;
logic [6*LEN-1:0] itch_order_delete_timestamp_o;
logic [8*LEN-1:0] itch_order_delete_order_reference_number_o;

logic itch_order_replace_v_o;
logic [2*LEN-1:0] itch_order_replace_stock_locate_o;
logic [2*LEN-1:0] itch_order_replace_tracking_number_o;
logic [6*LEN-1:0] itch_order_replace_timestamp_o;
logic [8*LEN-1:0] itch_order_replace_original_order_reference_number_o;
logic [8*LEN-1:0] itch_order_replace_new_order_reference_number_o;
logic [4*LEN-1:0] itch_order_replace_shares_o;
logic [4*LEN-1:0] itch_order_replace_price_o;

logic itch_trade_v_o;
logic [2*LEN-1:0] itch_trade_stock_locate_o;
logic [2*LEN-1:0] itch_trade_tracking_number_o;
logic [6*LEN-1:0] itch_trade_timestamp_o;
logic [8*LEN-1:0] itch_trade_order_reference_number_o;
logic [1*LEN-1:0] itch_trade_buy_sell_indicator_o;
logic [4*LEN-1:0] itch_trade_shares_o;
logic [8*LEN-1:0] itch_trade_stock_o;
logic [4*LEN-1:0] itch_trade_price_o;
logic [8*LEN-1:0] itch_trade_match_number_o;

logic itch_cross_trade_v_o;
logic [2*LEN-1:0] itch_cross_trade_stock_locate_o;
logic [2*LEN-1:0] itch_cross_trade_tracking_number_o;
logic [6*LEN-1:0] itch_cross_trade_timestamp_o;
logic [8*LEN-1:0] itch_cross_trade_shares_o;
logic [8*LEN-1:0] itch_cross_trade_stock_o;
logic [4*LEN-1:0] itch_cross_trade_cross_price_o;
logic [8*LEN-1:0] itch_cross_trade_match_number_o;
logic [1*LEN-1:0] itch_cross_trade_cross_type_o;

logic itch_broken_trade_v_o;
logic [2*LEN-1:0] itch_broken_trade_stock_locate_o;
logic [2*LEN-1:0] itch_broken_trade_tracking_number_o;
logic [6*LEN-1:0] itch_broken_trade_timestamp_o;
logic [8*LEN-1:0] itch_broken_trade_match_number_o;

logic itch_net_order_imbalance_indicator_v_o;
logic [2*LEN-1:0] itch_net_order_imbalance_indicator_stock_locate_o;
logic [2*LEN-1:0] itch_net_order_imbalance_indicator_tracking_number_o;
logic [6*LEN-1:0] itch_net_order_imbalance_indicator_timestamp_o;
logic [8*LEN-1:0] itch_net_order_imbalance_indicator_paired_shares_o;
logic [8*LEN-1:0] itch_net_order_imbalance_indicator_imbalance_shares_o;
logic [1*LEN-1:0] itch_net_order_imbalance_indicator_imbalance_direction_o;
logic [8*LEN-1:0] itch_net_order_imbalance_indicator_stock_o;
logic [4*LEN-1:0] itch_net_order_imbalance_indicator_far_price_o;
logic [4*LEN-1:0] itch_net_order_imbalance_indicator_near_price_o;
logic [4*LEN-1:0] itch_net_order_imbalance_indicator_current_reference_price_o;
logic [1*LEN-1:0] itch_net_order_imbalance_indicator_cross_type_o;
logic [1*LEN-1:0] itch_net_order_imbalance_indicator_price_variation_indicator_o;

logic itch_retail_price_improvement_indicator_v_o;
logic [2*LEN-1:0] itch_retail_price_improvement_indicator_stock_locate_o;
logic [2*LEN-1:0] itch_retail_price_improvement_indicator_tracking_number_o;
logic [6*LEN-1:0] itch_retail_price_improvement_indicator_timestamp_o;
logic [8*LEN-1:0] itch_retail_price_improvement_indicator_stock_o;
logic [1*LEN-1:0] itch_retail_price_improvement_indicator_interest_flag_o;

logic itch_end_of_snapshot_v_o;
logic [20*LEN-1:0] itch_end_of_snapshot_sequence_number_o;


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
	valid_i     = 1'b1;
	start_i = 1'b1;
	`ifdef DEBUG_ID
	tb_debug_id = { $random(), $random()};
	debug_id_i  = tb_debug_id;
	`endif
	// send simple end of snapshot msg, len = 21 bytes
	// will be sent over the next 3 cycles
	tb_msg_type  = "G"; 
	tb_eos_data  = {  5{32'hFFFFFFFF}};
	//tb_eos_data  = {5{32'hDEADBEAD}};
	data_i  = { tb_eos_data[AXI_DATA_W-LEN-1:0], tb_msg_type };
	len_i   = 'd8;
	#10
	start_i = 1'b0;
	data_i  = tb_eos_data[AXI_DATA_W*2-LEN-1:AXI_DATA_W-LEN];
	#10
	data_i  = { {AXI_DATA_W*3-LEN*21-1{1'bx}} , tb_eos_data[LEN*20-1:AXI_DATA_W*2-LEN] };
	len_i = 'd5;
 	// overlap
	ov_valid_i = 1'b1;
	tb_msg_type = "A";
	ov_data_i = { 'x , tb_msg_type};
	ov_len_i = 'd1;
	#10
	ov_valid_i = 1'b0;
	ov_len_i = 'x;
	data_i =  {8{8'haa}};
	len_i = 'd8;
	#10
	data_i =  {8{8'hbb}};
	#10
    data_i =  {8{8'hcc}};
	#10
	data_i =  {8{8'hdd}};
	#10
	data_i = { 'x, {3{8'hee}}};
	len_i = 'd3;
	#10
	valid_i = 1'b0;
	data_i = 'x;
	// check results
`ifdef GLIMPSE
	assert( itch_end_of_snapshot_v_o );
	assert( itch_end_of_snapshot_sequence_number_o == tb_eos_data );
`else
	// glimpse not supported, no message should have been seen
	assert( ~m_uut.itch_msg_sent );
`endif // GLIMPSE
`ifdef DEBUG_ID
	assert( debug_id_o == tb_debug_id );
`endif
	#20
	`ifdef DEBUG
	$display("Test end");
	`endif
	$finish;
end

tv_itch5_dec #( .LEN(LEN))
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
	.itch_system_event_v_o(itch_system_event_v_o),
	.itch_system_event_stock_locate_o(itch_system_event_stock_locate_o),
	.itch_system_event_tracking_number_o(itch_system_event_tracking_number_o),
	.itch_system_event_timestamp_o(itch_system_event_timestamp_o),
	.itch_system_event_event_code_o(itch_system_event_event_code_o),
	.itch_stock_directory_v_o(itch_stock_directory_v_o),
	.itch_stock_directory_stock_locate_o(itch_stock_directory_stock_locate_o),
	.itch_stock_directory_tracking_number_o(itch_stock_directory_tracking_number_o),
	.itch_stock_directory_timestamp_o(itch_stock_directory_timestamp_o),
	.itch_stock_directory_stock_o(itch_stock_directory_stock_o),
	.itch_stock_directory_market_category_o(itch_stock_directory_market_category_o),
	.itch_stock_directory_financial_status_indicator_o(itch_stock_directory_financial_status_indicator_o),
	.itch_stock_directory_round_lot_size_o(itch_stock_directory_round_lot_size_o),
	.itch_stock_directory_round_lots_only_o(itch_stock_directory_round_lots_only_o),
	.itch_stock_directory_issue_classification_o(itch_stock_directory_issue_classification_o),
	.itch_stock_directory_issue_sub_type_o(itch_stock_directory_issue_sub_type_o),
	.itch_stock_directory_authenticity_o(itch_stock_directory_authenticity_o),
	.itch_stock_directory_short_sale_threshold_indicator_o(itch_stock_directory_short_sale_threshold_indicator_o),
	.itch_stock_directory_ipo_flag_o(itch_stock_directory_ipo_flag_o),
	.itch_stock_directory_luld_reference_price_tier_o(itch_stock_directory_luld_reference_price_tier_o),
	.itch_stock_directory_etp_flag_o(itch_stock_directory_etp_flag_o),
	.itch_stock_directory_etp_leverage_factor_o(itch_stock_directory_etp_leverage_factor_o),
	.itch_stock_directory_inverse_indicator_o(itch_stock_directory_inverse_indicator_o),
	.itch_stock_trading_action_v_o(itch_stock_trading_action_v_o),
	.itch_stock_trading_action_stock_locate_o(itch_stock_trading_action_stock_locate_o),
	.itch_stock_trading_action_tracking_number_o(itch_stock_trading_action_tracking_number_o),
	.itch_stock_trading_action_timestamp_o(itch_stock_trading_action_timestamp_o),
	.itch_stock_trading_action_stock_o(itch_stock_trading_action_stock_o),
	.itch_stock_trading_action_trading_state_o(itch_stock_trading_action_trading_state_o),
	.itch_stock_trading_action_reserved_o(itch_stock_trading_action_reserved_o),
	.itch_stock_trading_action_reason_o(itch_stock_trading_action_reason_o),
	.itch_reg_sho_restriction_v_o(itch_reg_sho_restriction_v_o),
	.itch_reg_sho_restriction_stock_locate_o(itch_reg_sho_restriction_stock_locate_o),
	.itch_reg_sho_restriction_tracking_number_o(itch_reg_sho_restriction_tracking_number_o),
	.itch_reg_sho_restriction_timestamp_o(itch_reg_sho_restriction_timestamp_o),
	.itch_reg_sho_restriction_stock_o(itch_reg_sho_restriction_stock_o),
	.itch_reg_sho_restriction_reg_sho_action_o(itch_reg_sho_restriction_reg_sho_action_o),
	.itch_market_participant_position_v_o(itch_market_participant_position_v_o),
	.itch_market_participant_position_stock_locate_o(itch_market_participant_position_stock_locate_o),
	.itch_market_participant_position_tracking_number_o(itch_market_participant_position_tracking_number_o),
	.itch_market_participant_position_timestamp_o(itch_market_participant_position_timestamp_o),
	.itch_market_participant_position_mpid_o(itch_market_participant_position_mpid_o),
	.itch_market_participant_position_stock_o(itch_market_participant_position_stock_o),
	.itch_market_participant_position_primary_market_maker_o(itch_market_participant_position_primary_market_maker_o),
	.itch_market_participant_position_market_maker_mode_o(itch_market_participant_position_market_maker_mode_o),
	.itch_market_participant_position_market_participant_state_o(itch_market_participant_position_market_participant_state_o),
	.itch_mwcb_decline_level_v_o(itch_mwcb_decline_level_v_o),
	.itch_mwcb_decline_level_stock_locate_o(itch_mwcb_decline_level_stock_locate_o),
	.itch_mwcb_decline_level_tracking_number_o(itch_mwcb_decline_level_tracking_number_o),
	.itch_mwcb_decline_level_timestamp_o(itch_mwcb_decline_level_timestamp_o),
	.itch_mwcb_decline_level_level_1_o(itch_mwcb_decline_level_level_1_o),
	.itch_mwcb_decline_level_level_2_o(itch_mwcb_decline_level_level_2_o),
	.itch_mwcb_decline_level_level_3_o(itch_mwcb_decline_level_level_3_o),
	.itch_mwcb_status_v_o(itch_mwcb_status_v_o),
	.itch_mwcb_status_stock_locate_o(itch_mwcb_status_stock_locate_o),
	.itch_mwcb_status_tracking_number_o(itch_mwcb_status_tracking_number_o),
	.itch_mwcb_status_timestamp_o(itch_mwcb_status_timestamp_o),
	.itch_mwcb_status_breached_level_o(itch_mwcb_status_breached_level_o),
	.itch_ipo_quoting_period_update_v_o(itch_ipo_quoting_period_update_v_o),
	.itch_ipo_quoting_period_update_stock_locate_o(itch_ipo_quoting_period_update_stock_locate_o),
	.itch_ipo_quoting_period_update_tracking_number_o(itch_ipo_quoting_period_update_tracking_number_o),
	.itch_ipo_quoting_period_update_timestamp_o(itch_ipo_quoting_period_update_timestamp_o),
	.itch_ipo_quoting_period_update_stock_o(itch_ipo_quoting_period_update_stock_o),
	.itch_ipo_quoting_period_update_ipo_quotation_release_time_o(itch_ipo_quoting_period_update_ipo_quotation_release_time_o),
	.itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o(itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o),
	.itch_ipo_quoting_period_update_ipo_price_o(itch_ipo_quoting_period_update_ipo_price_o),
	.itch_luld_auction_collar_v_o(itch_luld_auction_collar_v_o),
	.itch_luld_auction_collar_stock_locate_o(itch_luld_auction_collar_stock_locate_o),
	.itch_luld_auction_collar_tracking_number_o(itch_luld_auction_collar_tracking_number_o),
	.itch_luld_auction_collar_timestamp_o(itch_luld_auction_collar_timestamp_o),
	.itch_luld_auction_collar_stock_o(itch_luld_auction_collar_stock_o),
	.itch_luld_auction_collar_auction_collar_reference_price_o(itch_luld_auction_collar_auction_collar_reference_price_o),
	.itch_luld_auction_collar_upper_auction_collar_price_o(itch_luld_auction_collar_upper_auction_collar_price_o),
	.itch_luld_auction_collar_lower_auction_collar_price_o(itch_luld_auction_collar_lower_auction_collar_price_o),
	.itch_luld_auction_collar_auction_collar_extension_o(itch_luld_auction_collar_auction_collar_extension_o),
	.itch_operational_halt_v_o(itch_operational_halt_v_o),
	.itch_operational_halt_stock_locate_o(itch_operational_halt_stock_locate_o),
	.itch_operational_halt_tracking_number_o(itch_operational_halt_tracking_number_o),
	.itch_operational_halt_timestamp_o(itch_operational_halt_timestamp_o),
	.itch_operational_halt_stock_o(itch_operational_halt_stock_o),
	.itch_operational_halt_market_code_o(itch_operational_halt_market_code_o),
	.itch_operational_halt_operational_halt_action_o(itch_operational_halt_operational_halt_action_o),
	.itch_add_order_v_o(itch_add_order_v_o),
	.itch_add_order_stock_locate_o(itch_add_order_stock_locate_o),
	.itch_add_order_tracking_number_o(itch_add_order_tracking_number_o),
	.itch_add_order_timestamp_o(itch_add_order_timestamp_o),
	.itch_add_order_order_reference_number_o(itch_add_order_order_reference_number_o),
	.itch_add_order_buy_sell_indicator_o(itch_add_order_buy_sell_indicator_o),
	.itch_add_order_shares_o(itch_add_order_shares_o),
	.itch_add_order_stock_o(itch_add_order_stock_o),
	.itch_add_order_price_o(itch_add_order_price_o),
	.itch_add_order_with_mpid_v_o(itch_add_order_with_mpid_v_o),
	.itch_add_order_with_mpid_stock_locate_o(itch_add_order_with_mpid_stock_locate_o),
	.itch_add_order_with_mpid_tracking_number_o(itch_add_order_with_mpid_tracking_number_o),
	.itch_add_order_with_mpid_timestamp_o(itch_add_order_with_mpid_timestamp_o),
	.itch_add_order_with_mpid_order_reference_number_o(itch_add_order_with_mpid_order_reference_number_o),
	.itch_add_order_with_mpid_buy_sell_indicator_o(itch_add_order_with_mpid_buy_sell_indicator_o),
	.itch_add_order_with_mpid_shares_o(itch_add_order_with_mpid_shares_o),
	.itch_add_order_with_mpid_stock_o(itch_add_order_with_mpid_stock_o),
	.itch_add_order_with_mpid_price_o(itch_add_order_with_mpid_price_o),
	.itch_add_order_with_mpid_attribution_o(itch_add_order_with_mpid_attribution_o),
	.itch_order_executed_v_o(itch_order_executed_v_o),
	.itch_order_executed_stock_locate_o(itch_order_executed_stock_locate_o),
	.itch_order_executed_tracking_number_o(itch_order_executed_tracking_number_o),
	.itch_order_executed_timestamp_o(itch_order_executed_timestamp_o),
	.itch_order_executed_order_reference_number_o(itch_order_executed_order_reference_number_o),
	.itch_order_executed_executed_shares_o(itch_order_executed_executed_shares_o),
	.itch_order_executed_match_number_o(itch_order_executed_match_number_o),
	.itch_order_executed_with_price_v_o(itch_order_executed_with_price_v_o),
	.itch_order_executed_with_price_stock_locate_o(itch_order_executed_with_price_stock_locate_o),
	.itch_order_executed_with_price_tracking_number_o(itch_order_executed_with_price_tracking_number_o),
	.itch_order_executed_with_price_timestamp_o(itch_order_executed_with_price_timestamp_o),
	.itch_order_executed_with_price_order_reference_number_o(itch_order_executed_with_price_order_reference_number_o),
	.itch_order_executed_with_price_executed_shares_o(itch_order_executed_with_price_executed_shares_o),
	.itch_order_executed_with_price_match_number_o(itch_order_executed_with_price_match_number_o),
	.itch_order_executed_with_price_printable_o(itch_order_executed_with_price_printable_o),
	.itch_order_executed_with_price_execution_price_o(itch_order_executed_with_price_execution_price_o),
	.itch_order_cancel_v_o(itch_order_cancel_v_o),
	.itch_order_cancel_stock_locate_o(itch_order_cancel_stock_locate_o),
	.itch_order_cancel_tracking_number_o(itch_order_cancel_tracking_number_o),
	.itch_order_cancel_timestamp_o(itch_order_cancel_timestamp_o),
	.itch_order_cancel_order_reference_number_o(itch_order_cancel_order_reference_number_o),
	.itch_order_cancel_cancelled_shares_o(itch_order_cancel_cancelled_shares_o),
	.itch_order_delete_v_o(itch_order_delete_v_o),
	.itch_order_delete_stock_locate_o(itch_order_delete_stock_locate_o),
	.itch_order_delete_tracking_number_o(itch_order_delete_tracking_number_o),
	.itch_order_delete_timestamp_o(itch_order_delete_timestamp_o),
	.itch_order_delete_order_reference_number_o(itch_order_delete_order_reference_number_o),
	.itch_order_replace_v_o(itch_order_replace_v_o),
	.itch_order_replace_stock_locate_o(itch_order_replace_stock_locate_o),
	.itch_order_replace_tracking_number_o(itch_order_replace_tracking_number_o),
	.itch_order_replace_timestamp_o(itch_order_replace_timestamp_o),
	.itch_order_replace_original_order_reference_number_o(itch_order_replace_original_order_reference_number_o),
	.itch_order_replace_new_order_reference_number_o(itch_order_replace_new_order_reference_number_o),
	.itch_order_replace_shares_o(itch_order_replace_shares_o),
	.itch_order_replace_price_o(itch_order_replace_price_o),
	.itch_trade_v_o(itch_trade_v_o),
	.itch_trade_stock_locate_o(itch_trade_stock_locate_o),
	.itch_trade_tracking_number_o(itch_trade_tracking_number_o),
	.itch_trade_timestamp_o(itch_trade_timestamp_o),
	.itch_trade_order_reference_number_o(itch_trade_order_reference_number_o),
	.itch_trade_buy_sell_indicator_o(itch_trade_buy_sell_indicator_o),
	.itch_trade_shares_o(itch_trade_shares_o),
	.itch_trade_stock_o(itch_trade_stock_o),
	.itch_trade_price_o(itch_trade_price_o),
	.itch_trade_match_number_o(itch_trade_match_number_o),
	.itch_cross_trade_v_o(itch_cross_trade_v_o),
	.itch_cross_trade_stock_locate_o(itch_cross_trade_stock_locate_o),
	.itch_cross_trade_tracking_number_o(itch_cross_trade_tracking_number_o),
	.itch_cross_trade_timestamp_o(itch_cross_trade_timestamp_o),
	.itch_cross_trade_shares_o(itch_cross_trade_shares_o),
	.itch_cross_trade_stock_o(itch_cross_trade_stock_o),
	.itch_cross_trade_cross_price_o(itch_cross_trade_cross_price_o),
	.itch_cross_trade_match_number_o(itch_cross_trade_match_number_o),
	.itch_cross_trade_cross_type_o(itch_cross_trade_cross_type_o),
	.itch_broken_trade_v_o(itch_broken_trade_v_o),
	.itch_broken_trade_stock_locate_o(itch_broken_trade_stock_locate_o),
	.itch_broken_trade_tracking_number_o(itch_broken_trade_tracking_number_o),
	.itch_broken_trade_timestamp_o(itch_broken_trade_timestamp_o),
	.itch_broken_trade_match_number_o(itch_broken_trade_match_number_o),
	.itch_net_order_imbalance_indicator_v_o(itch_net_order_imbalance_indicator_v_o),
	.itch_net_order_imbalance_indicator_stock_locate_o(itch_net_order_imbalance_indicator_stock_locate_o),
	.itch_net_order_imbalance_indicator_tracking_number_o(itch_net_order_imbalance_indicator_tracking_number_o),
	.itch_net_order_imbalance_indicator_timestamp_o(itch_net_order_imbalance_indicator_timestamp_o),
	.itch_net_order_imbalance_indicator_paired_shares_o(itch_net_order_imbalance_indicator_paired_shares_o),
	.itch_net_order_imbalance_indicator_imbalance_shares_o(itch_net_order_imbalance_indicator_imbalance_shares_o),
	.itch_net_order_imbalance_indicator_imbalance_direction_o(itch_net_order_imbalance_indicator_imbalance_direction_o),
	.itch_net_order_imbalance_indicator_stock_o(itch_net_order_imbalance_indicator_stock_o),
	.itch_net_order_imbalance_indicator_far_price_o(itch_net_order_imbalance_indicator_far_price_o),
	.itch_net_order_imbalance_indicator_near_price_o(itch_net_order_imbalance_indicator_near_price_o),
	.itch_net_order_imbalance_indicator_current_reference_price_o(itch_net_order_imbalance_indicator_current_reference_price_o),
	.itch_net_order_imbalance_indicator_cross_type_o(itch_net_order_imbalance_indicator_cross_type_o),
	.itch_net_order_imbalance_indicator_price_variation_indicator_o(itch_net_order_imbalance_indicator_price_variation_indicator_o),
`ifdef GLIMPSE
	.itch_end_of_snapshot_v_o(itch_end_of_snapshot_v_o),
	.itch_end_of_snapshot_sequence_number_o(itch_end_of_snapshot_sequence_number_o),
`endif
	.itch_retail_price_improvement_indicator_v_o(itch_retail_price_improvement_indicator_v_o),	
	.itch_retail_price_improvement_indicator_stock_locate_o(itch_retail_price_improvement_indicator_stock_locate_o),
	.itch_retail_price_improvement_indicator_tracking_number_o(itch_retail_price_improvement_indicator_tracking_number_o),
	.itch_retail_price_improvement_indicator_timestamp_o(itch_retail_price_improvement_indicator_timestamp_o),
	.itch_retail_price_improvement_indicator_stock_o(itch_retail_price_improvement_indicator_stock_o),
	.itch_retail_price_improvement_indicator_interest_flag_o(itch_retail_price_improvement_indicator_interest_flag_o)
);
endmodule

