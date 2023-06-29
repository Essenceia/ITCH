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
	input [ITCH_N*AXI_DATA_W-1:0] data_i,

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
`ifdef EARLY
logic [ITCH_N-1:0] dec_system_event_early_v;
logic [ITCH_N-1:0] dec_system_event_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_system_event_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_system_event_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_system_event_event_code_early_lite_v;

logic [ITCH_N-1:0] dec_stock_directory_early_v;
logic [ITCH_N-1:0] dec_stock_directory_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_stock_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_market_category_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_financial_status_indicator_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_round_lot_size_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_round_lots_only_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_issue_classification_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_issue_sub_type_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_authenticity_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_short_sale_threshold_indicator_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_ipo_flag_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_luld_reference_price_tier_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_etp_flag_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_etp_leverage_factor_early_lite_v;
logic [ITCH_N-1:0] dec_stock_directory_inverse_indicator_early_lite_v;

logic [ITCH_N-1:0] dec_stock_trading_action_early_v;
logic [ITCH_N-1:0] dec_stock_trading_action_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_stock_trading_action_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_stock_trading_action_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_stock_trading_action_stock_early_lite_v;
logic [ITCH_N-1:0] dec_stock_trading_action_trading_state_early_lite_v;
logic [ITCH_N-1:0] dec_stock_trading_action_reserved_early_lite_v;
logic [ITCH_N-1:0] dec_stock_trading_action_reason_early_lite_v;

logic [ITCH_N-1:0] dec_reg_sho_restriction_early_v;
logic [ITCH_N-1:0] dec_reg_sho_restriction_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_reg_sho_restriction_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_reg_sho_restriction_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_reg_sho_restriction_stock_early_lite_v;
logic [ITCH_N-1:0] dec_reg_sho_restriction_reg_sho_action_early_lite_v;

logic [ITCH_N-1:0] dec_market_participant_position_early_v;
logic [ITCH_N-1:0] dec_market_participant_position_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_mpid_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_stock_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_primary_market_maker_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_market_maker_mode_early_lite_v;
logic [ITCH_N-1:0] dec_market_participant_position_market_participant_state_early_lite_v;

logic [ITCH_N-1:0] dec_mwcb_decline_level_early_v;
logic [ITCH_N-1:0] dec_mwcb_decline_level_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_decline_level_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_decline_level_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_decline_level_level_1_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_decline_level_level_2_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_decline_level_level_3_early_lite_v;

logic [ITCH_N-1:0] dec_mwcb_status_early_v;
logic [ITCH_N-1:0] dec_mwcb_status_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_status_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_status_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_mwcb_status_breached_level_early_lite_v;

logic [ITCH_N-1:0] dec_ipo_quoting_period_update_early_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_stock_early_lite_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_ipo_quotation_release_time_early_lite_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_ipo_quotation_release_qualifier_early_lite_v;
logic [ITCH_N-1:0] dec_ipo_quoting_period_update_ipo_price_early_lite_v;

logic [ITCH_N-1:0] dec_luld_auction_collar_early_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_stock_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_auction_collar_reference_price_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_upper_auction_collar_price_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_lower_auction_collar_price_early_lite_v;
logic [ITCH_N-1:0] dec_luld_auction_collar_auction_collar_extension_early_lite_v;

logic [ITCH_N-1:0] dec_operational_halt_early_v;
logic [ITCH_N-1:0] dec_operational_halt_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_operational_halt_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_operational_halt_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_operational_halt_stock_early_lite_v;
logic [ITCH_N-1:0] dec_operational_halt_market_code_early_lite_v;
logic [ITCH_N-1:0] dec_operational_halt_operational_halt_action_early_lite_v;

logic [ITCH_N-1:0] dec_add_order_early_v;
logic [ITCH_N-1:0] dec_add_order_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_buy_sell_indicator_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_shares_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_stock_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_price_early_lite_v;

logic [ITCH_N-1:0] dec_add_order_with_mpid_early_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_buy_sell_indicator_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_shares_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_stock_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_price_early_lite_v;
logic [ITCH_N-1:0] dec_add_order_with_mpid_attribution_early_lite_v;

logic [ITCH_N-1:0] dec_order_executed_early_v;
logic [ITCH_N-1:0] dec_order_executed_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_executed_shares_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_match_number_early_lite_v;

logic [ITCH_N-1:0] dec_order_executed_with_price_early_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_executed_shares_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_match_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_printable_early_lite_v;
logic [ITCH_N-1:0] dec_order_executed_with_price_execution_price_early_lite_v;

logic [ITCH_N-1:0] dec_order_cancel_early_v;
logic [ITCH_N-1:0] dec_order_cancel_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_order_cancel_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_cancel_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_order_cancel_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_cancel_cancelled_shares_early_lite_v;

logic [ITCH_N-1:0] dec_order_delete_early_v;
logic [ITCH_N-1:0] dec_order_delete_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_order_delete_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_delete_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_order_delete_order_reference_number_early_lite_v;

logic [ITCH_N-1:0] dec_order_replace_early_v;
logic [ITCH_N-1:0] dec_order_replace_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_order_replace_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_replace_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_order_replace_original_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_replace_new_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_order_replace_shares_early_lite_v;
logic [ITCH_N-1:0] dec_order_replace_price_early_lite_v;

logic [ITCH_N-1:0] dec_trade_early_v;
logic [ITCH_N-1:0] dec_trade_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_trade_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_trade_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_trade_order_reference_number_early_lite_v;
logic [ITCH_N-1:0] dec_trade_buy_sell_indicator_early_lite_v;
logic [ITCH_N-1:0] dec_trade_shares_early_lite_v;
logic [ITCH_N-1:0] dec_trade_stock_early_lite_v;
logic [ITCH_N-1:0] dec_trade_price_early_lite_v;
logic [ITCH_N-1:0] dec_trade_match_number_early_lite_v;

logic [ITCH_N-1:0] dec_cross_trade_early_v;
logic [ITCH_N-1:0] dec_cross_trade_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_shares_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_stock_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_cross_price_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_match_number_early_lite_v;
logic [ITCH_N-1:0] dec_cross_trade_cross_type_early_lite_v;

logic [ITCH_N-1:0] dec_broken_trade_early_v;
logic [ITCH_N-1:0] dec_broken_trade_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_broken_trade_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_broken_trade_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_broken_trade_match_number_early_lite_v;

logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_early_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_paired_shares_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_imbalance_shares_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_imbalance_direction_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_stock_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_far_price_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_near_price_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_current_reference_price_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_cross_type_early_lite_v;
logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_price_variation_indicator_early_lite_v;

logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_early_v;
logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_stock_locate_early_lite_v;
logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_tracking_number_early_lite_v;
logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_timestamp_early_lite_v;
logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_stock_early_lite_v;
logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_interest_flag_early_lite_v;

`ifdef GLIMPSE
logic [ITCH_N-1:0] dec_end_of_snapshot_early_v;
logic [ITCH_N-1:0] dec_end_of_snapshot_sequence_number_early_lite_v;
`endif // GLIMPSE
`endif // EARLY

logic [ITCH_N-1:0] dec_system_event_v;
logic [ITCH_N*2*LEN-1:0] dec_system_event_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_system_event_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_system_event_timestamp;
logic [ITCH_N*1*LEN-1:0] dec_system_event_event_code;

logic [ITCH_N-1:0] dec_stock_directory_v;
logic [ITCH_N*2*LEN-1:0] dec_stock_directory_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_stock_directory_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_stock_directory_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_stock_directory_stock;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_market_category;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_financial_status_indicator;
logic [ITCH_N*4*LEN-1:0] dec_stock_directory_round_lot_size;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_round_lots_only;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_issue_classification;
logic [ITCH_N*2*LEN-1:0] dec_stock_directory_issue_sub_type;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_authenticity;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_short_sale_threshold_indicator;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_ipo_flag;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_luld_reference_price_tier;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_etp_flag;
logic [ITCH_N*4*LEN-1:0] dec_stock_directory_etp_leverage_factor;
logic [ITCH_N*1*LEN-1:0] dec_stock_directory_inverse_indicator;

logic [ITCH_N-1:0] dec_stock_trading_action_v;
logic [ITCH_N*2*LEN-1:0] dec_stock_trading_action_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_stock_trading_action_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_stock_trading_action_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_stock_trading_action_stock;
logic [ITCH_N*1*LEN-1:0] dec_stock_trading_action_trading_state;
logic [ITCH_N*1*LEN-1:0] dec_stock_trading_action_reserved;
logic [ITCH_N*4*LEN-1:0] dec_stock_trading_action_reason;

logic [ITCH_N-1:0] dec_reg_sho_restriction_v;
logic [ITCH_N*2*LEN-1:0] dec_reg_sho_restriction_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_reg_sho_restriction_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_reg_sho_restriction_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_reg_sho_restriction_stock;
logic [ITCH_N*1*LEN-1:0] dec_reg_sho_restriction_reg_sho_action;

logic [ITCH_N-1:0] dec_market_participant_position_v;
logic [ITCH_N*2*LEN-1:0] dec_market_participant_position_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_market_participant_position_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_market_participant_position_timestamp;
logic [ITCH_N*4*LEN-1:0] dec_market_participant_position_mpid;
logic [ITCH_N*8*LEN-1:0] dec_market_participant_position_stock;
logic [ITCH_N*1*LEN-1:0] dec_market_participant_position_primary_market_maker;
logic [ITCH_N*1*LEN-1:0] dec_market_participant_position_market_maker_mode;
logic [ITCH_N*1*LEN-1:0] dec_market_participant_position_market_participant_state;

logic [ITCH_N-1:0] dec_mwcb_decline_level_v;
logic [ITCH_N*2*LEN-1:0] dec_mwcb_decline_level_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_mwcb_decline_level_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_mwcb_decline_level_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_mwcb_decline_level_level_1;
logic [ITCH_N*8*LEN-1:0] dec_mwcb_decline_level_level_2;
logic [ITCH_N*8*LEN-1:0] dec_mwcb_decline_level_level_3;

logic [ITCH_N-1:0] dec_mwcb_status_v;
logic [ITCH_N*2*LEN-1:0] dec_mwcb_status_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_mwcb_status_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_mwcb_status_timestamp;
logic [ITCH_N*1*LEN-1:0] dec_mwcb_status_breached_level;

logic [ITCH_N-1:0] dec_ipo_quoting_period_update_v;
logic [ITCH_N*2*LEN-1:0] dec_ipo_quoting_period_update_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_ipo_quoting_period_update_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_ipo_quoting_period_update_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_ipo_quoting_period_update_stock;
logic [ITCH_N*4*LEN-1:0] dec_ipo_quoting_period_update_ipo_quotation_release_time;
logic [ITCH_N*1*LEN-1:0] dec_ipo_quoting_period_update_ipo_quotation_release_qualifier;
logic [ITCH_N*4*LEN-1:0] dec_ipo_quoting_period_update_ipo_price;

logic [ITCH_N-1:0] dec_luld_auction_collar_v;
logic [ITCH_N*2*LEN-1:0] dec_luld_auction_collar_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_luld_auction_collar_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_luld_auction_collar_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_luld_auction_collar_stock;
logic [ITCH_N*4*LEN-1:0] dec_luld_auction_collar_auction_collar_reference_price;
logic [ITCH_N*4*LEN-1:0] dec_luld_auction_collar_upper_auction_collar_price;
logic [ITCH_N*4*LEN-1:0] dec_luld_auction_collar_lower_auction_collar_price;
logic [ITCH_N*4*LEN-1:0] dec_luld_auction_collar_auction_collar_extension;

logic [ITCH_N-1:0] dec_operational_halt_v;
logic [ITCH_N*2*LEN-1:0] dec_operational_halt_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_operational_halt_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_operational_halt_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_operational_halt_stock;
logic [ITCH_N*1*LEN-1:0] dec_operational_halt_market_code;
logic [ITCH_N*1*LEN-1:0] dec_operational_halt_operational_halt_action;

logic [ITCH_N-1:0] dec_add_order_v;
logic [ITCH_N*2*LEN-1:0] dec_add_order_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_add_order_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_add_order_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_add_order_order_reference_number;
logic [ITCH_N*1*LEN-1:0] dec_add_order_buy_sell_indicator;
logic [ITCH_N*4*LEN-1:0] dec_add_order_shares;
logic [ITCH_N*8*LEN-1:0] dec_add_order_stock;
logic [ITCH_N*4*LEN-1:0] dec_add_order_price;

logic [ITCH_N-1:0] dec_add_order_with_mpid_v;
logic [ITCH_N*2*LEN-1:0] dec_add_order_with_mpid_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_add_order_with_mpid_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_add_order_with_mpid_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_add_order_with_mpid_order_reference_number;
logic [ITCH_N*1*LEN-1:0] dec_add_order_with_mpid_buy_sell_indicator;
logic [ITCH_N*4*LEN-1:0] dec_add_order_with_mpid_shares;
logic [ITCH_N*8*LEN-1:0] dec_add_order_with_mpid_stock;
logic [ITCH_N*4*LEN-1:0] dec_add_order_with_mpid_price;
logic [ITCH_N*4*LEN-1:0] dec_add_order_with_mpid_attribution;

logic [ITCH_N-1:0] dec_order_executed_v;
logic [ITCH_N*2*LEN-1:0] dec_order_executed_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_order_executed_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_order_executed_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_order_executed_order_reference_number;
logic [ITCH_N*4*LEN-1:0] dec_order_executed_executed_shares;
logic [ITCH_N*8*LEN-1:0] dec_order_executed_match_number;

logic [ITCH_N-1:0] dec_order_executed_with_price_v;
logic [ITCH_N*2*LEN-1:0] dec_order_executed_with_price_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_order_executed_with_price_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_order_executed_with_price_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_order_executed_with_price_order_reference_number;
logic [ITCH_N*4*LEN-1:0] dec_order_executed_with_price_executed_shares;
logic [ITCH_N*8*LEN-1:0] dec_order_executed_with_price_match_number;
logic [ITCH_N*1*LEN-1:0] dec_order_executed_with_price_printable;
logic [ITCH_N*4*LEN-1:0] dec_order_executed_with_price_execution_price;

logic [ITCH_N-1:0] dec_order_cancel_v;
logic [ITCH_N*2*LEN-1:0] dec_order_cancel_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_order_cancel_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_order_cancel_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_order_cancel_order_reference_number;
logic [ITCH_N*4*LEN-1:0] dec_order_cancel_cancelled_shares;

logic [ITCH_N-1:0] dec_order_delete_v;
logic [ITCH_N*2*LEN-1:0] dec_order_delete_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_order_delete_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_order_delete_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_order_delete_order_reference_number;

logic [ITCH_N-1:0] dec_order_replace_v;
logic [ITCH_N*2*LEN-1:0] dec_order_replace_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_order_replace_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_order_replace_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_order_replace_original_order_reference_number;
logic [ITCH_N*8*LEN-1:0] dec_order_replace_new_order_reference_number;
logic [ITCH_N*4*LEN-1:0] dec_order_replace_shares;
logic [ITCH_N*4*LEN-1:0] dec_order_replace_price;

logic [ITCH_N-1:0] dec_trade_v;
logic [ITCH_N*2*LEN-1:0] dec_trade_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_trade_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_trade_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_trade_order_reference_number;
logic [ITCH_N*1*LEN-1:0] dec_trade_buy_sell_indicator;
logic [ITCH_N*4*LEN-1:0] dec_trade_shares;
logic [ITCH_N*8*LEN-1:0] dec_trade_stock;
logic [ITCH_N*4*LEN-1:0] dec_trade_price;
logic [ITCH_N*8*LEN-1:0] dec_trade_match_number;

logic [ITCH_N-1:0] dec_cross_trade_v;
logic [ITCH_N*2*LEN-1:0] dec_cross_trade_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_cross_trade_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_cross_trade_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_cross_trade_shares;
logic [ITCH_N*8*LEN-1:0] dec_cross_trade_stock;
logic [ITCH_N*4*LEN-1:0] dec_cross_trade_cross_price;
logic [ITCH_N*8*LEN-1:0] dec_cross_trade_match_number;
logic [ITCH_N*1*LEN-1:0] dec_cross_trade_cross_type;

logic [ITCH_N-1:0] dec_broken_trade_v;
logic [ITCH_N*2*LEN-1:0] dec_broken_trade_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_broken_trade_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_broken_trade_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_broken_trade_match_number;

logic [ITCH_N-1:0] dec_net_order_imbalance_indicator_v;
logic [ITCH_N*2*LEN-1:0] dec_net_order_imbalance_indicator_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_net_order_imbalance_indicator_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_net_order_imbalance_indicator_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_net_order_imbalance_indicator_paired_shares;
logic [ITCH_N*8*LEN-1:0] dec_net_order_imbalance_indicator_imbalance_shares;
logic [ITCH_N*1*LEN-1:0] dec_net_order_imbalance_indicator_imbalance_direction;
logic [ITCH_N*8*LEN-1:0] dec_net_order_imbalance_indicator_stock;
logic [ITCH_N*4*LEN-1:0] dec_net_order_imbalance_indicator_far_price;
logic [ITCH_N*4*LEN-1:0] dec_net_order_imbalance_indicator_near_price;
logic [ITCH_N*4*LEN-1:0] dec_net_order_imbalance_indicator_current_reference_price;
logic [ITCH_N*1*LEN-1:0] dec_net_order_imbalance_indicator_cross_type;
logic [ITCH_N*1*LEN-1:0] dec_net_order_imbalance_indicator_price_variation_indicator;

`ifdef GLIMPSE
logic [ITCH_N-1:0] dec_end_of_snapshot_v;
logic [ITCH_N*20*LEN-1:0] dec_end_of_snapshot_sequence_number;
`endif

logic [ITCH_N-1:0] dec_retail_price_improvement_indicator_v;
logic [ITCH_N*2*LEN-1:0] dec_retail_price_improvement_indicator_stock_locate;
logic [ITCH_N*2*LEN-1:0] dec_retail_price_improvement_indicator_tracking_number;
logic [ITCH_N*6*LEN-1:0] dec_retail_price_improvement_indicator_timestamp;
logic [ITCH_N*8*LEN-1:0] dec_retail_price_improvement_indicator_stock;
logic [ITCH_N*1*LEN-1:0] dec_retail_price_improvement_indicator_interest_flag;

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
			.len_i  (len_i[i*KEEP_LW+KEEP_LW-1:i*KEEP_LW]),

			`ifdef EARLY
			.itch_system_event_early_v_o(dec_system_event_early_v[i]),
			.itch_system_event_stock_locate_early_lite_v_o(dec_system_event_stock_locate_early_lite_v[i]),
			.itch_system_event_tracking_number_early_lite_v_o(dec_system_event_tracking_number_early_lite_v[i]),
			.itch_system_event_timestamp_early_lite_v_o(dec_system_event_timestamp_early_lite_v[i]),
			.itch_system_event_event_code_early_lite_v_o(dec_system_event_event_code_early_lite_v[i]),
			
			.itch_stock_directory_early_v_o(dec_stock_directory_early_v[i]),
			.itch_stock_directory_stock_locate_early_lite_v_o(dec_stock_directory_stock_locate_early_lite_v[i]),
			.itch_stock_directory_tracking_number_early_lite_v_o(dec_stock_directory_tracking_number_early_lite_v[i]),
			.itch_stock_directory_timestamp_early_lite_v_o(dec_stock_directory_timestamp_early_lite_v[i]),
			.itch_stock_directory_stock_early_lite_v_o(dec_stock_directory_stock_early_lite_v[i]),
			.itch_stock_directory_market_category_early_lite_v_o(dec_stock_directory_market_category_early_lite_v[i]),
			.itch_stock_directory_financial_status_indicator_early_lite_v_o(dec_stock_directory_financial_status_indicator_early_lite_v[i]),
			.itch_stock_directory_round_lot_size_early_lite_v_o(dec_stock_directory_round_lot_size_early_lite_v[i]),
			.itch_stock_directory_round_lots_only_early_lite_v_o(dec_stock_directory_round_lots_only_early_lite_v[i]),
			.itch_stock_directory_issue_classification_early_lite_v_o(dec_stock_directory_issue_classification_early_lite_v[i]),
			.itch_stock_directory_issue_sub_type_early_lite_v_o(dec_stock_directory_issue_sub_type_early_lite_v[i]),
			.itch_stock_directory_authenticity_early_lite_v_o(dec_stock_directory_authenticity_early_lite_v[i]),
			.itch_stock_directory_short_sale_threshold_indicator_early_lite_v_o(dec_stock_directory_short_sale_threshold_indicator_early_lite_v[i]),
			.itch_stock_directory_ipo_flag_early_lite_v_o(dec_stock_directory_ipo_flag_early_lite_v[i]),
			.itch_stock_directory_luld_reference_price_tier_early_lite_v_o(dec_stock_directory_luld_reference_price_tier_early_lite_v[i]),
			.itch_stock_directory_etp_flag_early_lite_v_o(dec_stock_directory_etp_flag_early_lite_v[i]),
			.itch_stock_directory_etp_leverage_factor_early_lite_v_o(dec_stock_directory_etp_leverage_factor_early_lite_v[i]),
			.itch_stock_directory_inverse_indicator_early_lite_v_o(dec_stock_directory_inverse_indicator_early_lite_v[i]),
			
			.itch_stock_trading_action_early_v_o(dec_stock_trading_action_early_v[i]),
			.itch_stock_trading_action_stock_locate_early_lite_v_o(dec_stock_trading_action_stock_locate_early_lite_v[i]),
			.itch_stock_trading_action_tracking_number_early_lite_v_o(dec_stock_trading_action_tracking_number_early_lite_v[i]),
			.itch_stock_trading_action_timestamp_early_lite_v_o(dec_stock_trading_action_timestamp_early_lite_v[i]),
			.itch_stock_trading_action_stock_early_lite_v_o(dec_stock_trading_action_stock_early_lite_v[i]),
			.itch_stock_trading_action_trading_state_early_lite_v_o(dec_stock_trading_action_trading_state_early_lite_v[i]),
			.itch_stock_trading_action_reserved_early_lite_v_o(dec_stock_trading_action_reserved_early_lite_v[i]),
			.itch_stock_trading_action_reason_early_lite_v_o(dec_stock_trading_action_reason_early_lite_v[i]),
			
			.itch_reg_sho_restriction_early_v_o(dec_reg_sho_restriction_early_v[i]),
			.itch_reg_sho_restriction_stock_locate_early_lite_v_o(dec_reg_sho_restriction_stock_locate_early_lite_v[i]),
			.itch_reg_sho_restriction_tracking_number_early_lite_v_o(dec_reg_sho_restriction_tracking_number_early_lite_v[i]),
			.itch_reg_sho_restriction_timestamp_early_lite_v_o(dec_reg_sho_restriction_timestamp_early_lite_v[i]),
			.itch_reg_sho_restriction_stock_early_lite_v_o(dec_reg_sho_restriction_stock_early_lite_v[i]),
			.itch_reg_sho_restriction_reg_sho_action_early_lite_v_o(dec_reg_sho_restriction_reg_sho_action_early_lite_v[i]),
			
			.itch_market_participant_position_early_v_o(dec_market_participant_position_early_v[i]),
			.itch_market_participant_position_stock_locate_early_lite_v_o(dec_market_participant_position_stock_locate_early_lite_v[i]),
			.itch_market_participant_position_tracking_number_early_lite_v_o(dec_market_participant_position_tracking_number_early_lite_v[i]),
			.itch_market_participant_position_timestamp_early_lite_v_o(dec_market_participant_position_timestamp_early_lite_v[i]),
			.itch_market_participant_position_mpid_early_lite_v_o(dec_market_participant_position_mpid_early_lite_v[i]),
			.itch_market_participant_position_stock_early_lite_v_o(dec_market_participant_position_stock_early_lite_v[i]),
			.itch_market_participant_position_primary_market_maker_early_lite_v_o(dec_market_participant_position_primary_market_maker_early_lite_v[i]),
			.itch_market_participant_position_market_maker_mode_early_lite_v_o(dec_market_participant_position_market_maker_mode_early_lite_v[i]),
			.itch_market_participant_position_market_participant_state_early_lite_v_o(dec_market_participant_position_market_participant_state_early_lite_v[i]),
			
			.itch_mwcb_decline_level_early_v_o(dec_mwcb_decline_level_early_v[i]),
			.itch_mwcb_decline_level_stock_locate_early_lite_v_o(dec_mwcb_decline_level_stock_locate_early_lite_v[i]),
			.itch_mwcb_decline_level_tracking_number_early_lite_v_o(dec_mwcb_decline_level_tracking_number_early_lite_v[i]),
			.itch_mwcb_decline_level_timestamp_early_lite_v_o(dec_mwcb_decline_level_timestamp_early_lite_v[i]),
			.itch_mwcb_decline_level_level_1_early_lite_v_o(dec_mwcb_decline_level_level_1_early_lite_v[i]),
			.itch_mwcb_decline_level_level_2_early_lite_v_o(dec_mwcb_decline_level_level_2_early_lite_v[i]),
			.itch_mwcb_decline_level_level_3_early_lite_v_o(dec_mwcb_decline_level_level_3_early_lite_v[i]),
			
			.itch_mwcb_status_early_v_o(dec_mwcb_status_early_v[i]),
			.itch_mwcb_status_stock_locate_early_lite_v_o(dec_mwcb_status_stock_locate_early_lite_v[i]),
			.itch_mwcb_status_tracking_number_early_lite_v_o(dec_mwcb_status_tracking_number_early_lite_v[i]),
			.itch_mwcb_status_timestamp_early_lite_v_o(dec_mwcb_status_timestamp_early_lite_v[i]),
			.itch_mwcb_status_breached_level_early_lite_v_o(dec_mwcb_status_breached_level_early_lite_v[i]),
			
			.itch_ipo_quoting_period_update_early_v_o(dec_ipo_quoting_period_update_early_v[i]),
			.itch_ipo_quoting_period_update_stock_locate_early_lite_v_o(dec_ipo_quoting_period_update_stock_locate_early_lite_v[i]),
			.itch_ipo_quoting_period_update_tracking_number_early_lite_v_o(dec_ipo_quoting_period_update_tracking_number_early_lite_v[i]),
			.itch_ipo_quoting_period_update_timestamp_early_lite_v_o(dec_ipo_quoting_period_update_timestamp_early_lite_v[i]),
			.itch_ipo_quoting_period_update_stock_early_lite_v_o(dec_ipo_quoting_period_update_stock_early_lite_v[i]),
			.itch_ipo_quoting_period_update_ipo_quotation_release_time_early_lite_v_o(dec_ipo_quoting_period_update_ipo_quotation_release_time_early_lite_v[i]),
			.itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_early_lite_v_o(dec_ipo_quoting_period_update_ipo_quotation_release_qualifier_early_lite_v[i]),
			.itch_ipo_quoting_period_update_ipo_price_early_lite_v_o(dec_ipo_quoting_period_update_ipo_price_early_lite_v[i]),
			
			.itch_luld_auction_collar_early_v_o(dec_luld_auction_collar_early_v[i]),
			.itch_luld_auction_collar_stock_locate_early_lite_v_o(dec_luld_auction_collar_stock_locate_early_lite_v[i]),
			.itch_luld_auction_collar_tracking_number_early_lite_v_o(dec_luld_auction_collar_tracking_number_early_lite_v[i]),
			.itch_luld_auction_collar_timestamp_early_lite_v_o(dec_luld_auction_collar_timestamp_early_lite_v[i]),
			.itch_luld_auction_collar_stock_early_lite_v_o(dec_luld_auction_collar_stock_early_lite_v[i]),
			.itch_luld_auction_collar_auction_collar_reference_price_early_lite_v_o(dec_luld_auction_collar_auction_collar_reference_price_early_lite_v[i]),
			.itch_luld_auction_collar_upper_auction_collar_price_early_lite_v_o(dec_luld_auction_collar_upper_auction_collar_price_early_lite_v[i]),
			.itch_luld_auction_collar_lower_auction_collar_price_early_lite_v_o(dec_luld_auction_collar_lower_auction_collar_price_early_lite_v[i]),
			.itch_luld_auction_collar_auction_collar_extension_early_lite_v_o(dec_luld_auction_collar_auction_collar_extension_early_lite_v[i]),
			
			.itch_operational_halt_early_v_o(dec_operational_halt_early_v[i]),
			.itch_operational_halt_stock_locate_early_lite_v_o(dec_operational_halt_stock_locate_early_lite_v[i]),
			.itch_operational_halt_tracking_number_early_lite_v_o(dec_operational_halt_tracking_number_early_lite_v[i]),
			.itch_operational_halt_timestamp_early_lite_v_o(dec_operational_halt_timestamp_early_lite_v[i]),
			.itch_operational_halt_stock_early_lite_v_o(dec_operational_halt_stock_early_lite_v[i]),
			.itch_operational_halt_market_code_early_lite_v_o(dec_operational_halt_market_code_early_lite_v[i]),
			.itch_operational_halt_operational_halt_action_early_lite_v_o(dec_operational_halt_operational_halt_action_early_lite_v[i]),
			
			.itch_add_order_early_v_o(dec_add_order_early_v[i]),
			.itch_add_order_stock_locate_early_lite_v_o(dec_add_order_stock_locate_early_lite_v[i]),
			.itch_add_order_tracking_number_early_lite_v_o(dec_add_order_tracking_number_early_lite_v[i]),
			.itch_add_order_timestamp_early_lite_v_o(dec_add_order_timestamp_early_lite_v[i]),
			.itch_add_order_order_reference_number_early_lite_v_o(dec_add_order_order_reference_number_early_lite_v[i]),
			.itch_add_order_buy_sell_indicator_early_lite_v_o(dec_add_order_buy_sell_indicator_early_lite_v[i]),
			.itch_add_order_shares_early_lite_v_o(dec_add_order_shares_early_lite_v[i]),
			.itch_add_order_stock_early_lite_v_o(dec_add_order_stock_early_lite_v[i]),
			.itch_add_order_price_early_lite_v_o(dec_add_order_price_early_lite_v[i]),
			
			.itch_add_order_with_mpid_early_v_o(dec_add_order_with_mpid_early_v[i]),
			.itch_add_order_with_mpid_stock_locate_early_lite_v_o(dec_add_order_with_mpid_stock_locate_early_lite_v[i]),
			.itch_add_order_with_mpid_tracking_number_early_lite_v_o(dec_add_order_with_mpid_tracking_number_early_lite_v[i]),
			.itch_add_order_with_mpid_timestamp_early_lite_v_o(dec_add_order_with_mpid_timestamp_early_lite_v[i]),
			.itch_add_order_with_mpid_order_reference_number_early_lite_v_o(dec_add_order_with_mpid_order_reference_number_early_lite_v[i]),
			.itch_add_order_with_mpid_buy_sell_indicator_early_lite_v_o(dec_add_order_with_mpid_buy_sell_indicator_early_lite_v[i]),
			.itch_add_order_with_mpid_shares_early_lite_v_o(dec_add_order_with_mpid_shares_early_lite_v[i]),
			.itch_add_order_with_mpid_stock_early_lite_v_o(dec_add_order_with_mpid_stock_early_lite_v[i]),
			.itch_add_order_with_mpid_price_early_lite_v_o(dec_add_order_with_mpid_price_early_lite_v[i]),
			.itch_add_order_with_mpid_attribution_early_lite_v_o(dec_add_order_with_mpid_attribution_early_lite_v[i]),
			
			.itch_order_executed_early_v_o(dec_order_executed_early_v[i]),
			.itch_order_executed_stock_locate_early_lite_v_o(dec_order_executed_stock_locate_early_lite_v[i]),
			.itch_order_executed_tracking_number_early_lite_v_o(dec_order_executed_tracking_number_early_lite_v[i]),
			.itch_order_executed_timestamp_early_lite_v_o(dec_order_executed_timestamp_early_lite_v[i]),
			.itch_order_executed_order_reference_number_early_lite_v_o(dec_order_executed_order_reference_number_early_lite_v[i]),
			.itch_order_executed_executed_shares_early_lite_v_o(dec_order_executed_executed_shares_early_lite_v[i]),
			.itch_order_executed_match_number_early_lite_v_o(dec_order_executed_match_number_early_lite_v[i]),
			
			.itch_order_executed_with_price_early_v_o(dec_order_executed_with_price_early_v[i]),
			.itch_order_executed_with_price_stock_locate_early_lite_v_o(dec_order_executed_with_price_stock_locate_early_lite_v[i]),
			.itch_order_executed_with_price_tracking_number_early_lite_v_o(dec_order_executed_with_price_tracking_number_early_lite_v[i]),
			.itch_order_executed_with_price_timestamp_early_lite_v_o(dec_order_executed_with_price_timestamp_early_lite_v[i]),
			.itch_order_executed_with_price_order_reference_number_early_lite_v_o(dec_order_executed_with_price_order_reference_number_early_lite_v[i]),
			.itch_order_executed_with_price_executed_shares_early_lite_v_o(dec_order_executed_with_price_executed_shares_early_lite_v[i]),
			.itch_order_executed_with_price_match_number_early_lite_v_o(dec_order_executed_with_price_match_number_early_lite_v[i]),
			.itch_order_executed_with_price_printable_early_lite_v_o(dec_order_executed_with_price_printable_early_lite_v[i]),
			.itch_order_executed_with_price_execution_price_early_lite_v_o(dec_order_executed_with_price_execution_price_early_lite_v[i]),
			
			.itch_order_cancel_early_v_o(dec_order_cancel_early_v[i]),
			.itch_order_cancel_stock_locate_early_lite_v_o(dec_order_cancel_stock_locate_early_lite_v[i]),
			.itch_order_cancel_tracking_number_early_lite_v_o(dec_order_cancel_tracking_number_early_lite_v[i]),
			.itch_order_cancel_timestamp_early_lite_v_o(dec_order_cancel_timestamp_early_lite_v[i]),
			.itch_order_cancel_order_reference_number_early_lite_v_o(dec_order_cancel_order_reference_number_early_lite_v[i]),
			.itch_order_cancel_cancelled_shares_early_lite_v_o(dec_order_cancel_cancelled_shares_early_lite_v[i]),
			
			.itch_order_delete_early_v_o(dec_order_delete_early_v[i]),
			.itch_order_delete_stock_locate_early_lite_v_o(dec_order_delete_stock_locate_early_lite_v[i]),
			.itch_order_delete_tracking_number_early_lite_v_o(dec_order_delete_tracking_number_early_lite_v[i]),
			.itch_order_delete_timestamp_early_lite_v_o(dec_order_delete_timestamp_early_lite_v[i]),
			.itch_order_delete_order_reference_number_early_lite_v_o(dec_order_delete_order_reference_number_early_lite_v[i]),
			
			.itch_order_replace_early_v_o(dec_order_replace_early_v[i]),
			.itch_order_replace_stock_locate_early_lite_v_o(dec_order_replace_stock_locate_early_lite_v[i]),
			.itch_order_replace_tracking_number_early_lite_v_o(dec_order_replace_tracking_number_early_lite_v[i]),
			.itch_order_replace_timestamp_early_lite_v_o(dec_order_replace_timestamp_early_lite_v[i]),
			.itch_order_replace_original_order_reference_number_early_lite_v_o(dec_order_replace_original_order_reference_number_early_lite_v[i]),
			.itch_order_replace_new_order_reference_number_early_lite_v_o(dec_order_replace_new_order_reference_number_early_lite_v[i]),
			.itch_order_replace_shares_early_lite_v_o(dec_order_replace_shares_early_lite_v[i]),
			.itch_order_replace_price_early_lite_v_o(dec_order_replace_price_early_lite_v[i]),
			
			.itch_trade_early_v_o(dec_trade_early_v[i]),
			.itch_trade_stock_locate_early_lite_v_o(dec_trade_stock_locate_early_lite_v[i]),
			.itch_trade_tracking_number_early_lite_v_o(dec_trade_tracking_number_early_lite_v[i]),
			.itch_trade_timestamp_early_lite_v_o(dec_trade_timestamp_early_lite_v[i]),
			.itch_trade_order_reference_number_early_lite_v_o(dec_trade_order_reference_number_early_lite_v[i]),
			.itch_trade_buy_sell_indicator_early_lite_v_o(dec_trade_buy_sell_indicator_early_lite_v[i]),
			.itch_trade_shares_early_lite_v_o(dec_trade_shares_early_lite_v[i]),
			.itch_trade_stock_early_lite_v_o(dec_trade_stock_early_lite_v[i]),
			.itch_trade_price_early_lite_v_o(dec_trade_price_early_lite_v[i]),
			.itch_trade_match_number_early_lite_v_o(dec_trade_match_number_early_lite_v[i]),
			
			.itch_cross_trade_early_v_o(dec_cross_trade_early_v[i]),
			.itch_cross_trade_stock_locate_early_lite_v_o(dec_cross_trade_stock_locate_early_lite_v[i]),
			.itch_cross_trade_tracking_number_early_lite_v_o(dec_cross_trade_tracking_number_early_lite_v[i]),
			.itch_cross_trade_timestamp_early_lite_v_o(dec_cross_trade_timestamp_early_lite_v[i]),
			.itch_cross_trade_shares_early_lite_v_o(dec_cross_trade_shares_early_lite_v[i]),
			.itch_cross_trade_stock_early_lite_v_o(dec_cross_trade_stock_early_lite_v[i]),
			.itch_cross_trade_cross_price_early_lite_v_o(dec_cross_trade_cross_price_early_lite_v[i]),
			.itch_cross_trade_match_number_early_lite_v_o(dec_cross_trade_match_number_early_lite_v[i]),
			.itch_cross_trade_cross_type_early_lite_v_o(dec_cross_trade_cross_type_early_lite_v[i]),
			
			.itch_broken_trade_early_v_o(dec_broken_trade_early_v[i]),
			.itch_broken_trade_stock_locate_early_lite_v_o(dec_broken_trade_stock_locate_early_lite_v[i]),
			.itch_broken_trade_tracking_number_early_lite_v_o(dec_broken_trade_tracking_number_early_lite_v[i]),
			.itch_broken_trade_timestamp_early_lite_v_o(dec_broken_trade_timestamp_early_lite_v[i]),
			.itch_broken_trade_match_number_early_lite_v_o(dec_broken_trade_match_number_early_lite_v[i]),
			
			.itch_net_order_imbalance_indicator_early_v_o(dec_net_order_imbalance_indicator_early_v[i]),
			.itch_net_order_imbalance_indicator_stock_locate_early_lite_v_o(dec_net_order_imbalance_indicator_stock_locate_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_tracking_number_early_lite_v_o(dec_net_order_imbalance_indicator_tracking_number_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_timestamp_early_lite_v_o(dec_net_order_imbalance_indicator_timestamp_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_paired_shares_early_lite_v_o(dec_net_order_imbalance_indicator_paired_shares_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_imbalance_shares_early_lite_v_o(dec_net_order_imbalance_indicator_imbalance_shares_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_imbalance_direction_early_lite_v_o(dec_net_order_imbalance_indicator_imbalance_direction_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_stock_early_lite_v_o(dec_net_order_imbalance_indicator_stock_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_far_price_early_lite_v_o(dec_net_order_imbalance_indicator_far_price_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_near_price_early_lite_v_o(dec_net_order_imbalance_indicator_near_price_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_current_reference_price_early_lite_v_o(dec_net_order_imbalance_indicator_current_reference_price_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_cross_type_early_lite_v_o(dec_net_order_imbalance_indicator_cross_type_early_lite_v[i]),
			.itch_net_order_imbalance_indicator_price_variation_indicator_early_lite_v_o(dec_net_order_imbalance_indicator_price_variation_indicator_early_lite_v[i]),
			
			.itch_retail_price_improvement_indicator_early_v_o(dec_retail_price_improvement_indicator_early_v[i]),
			.itch_retail_price_improvement_indicator_stock_locate_early_lite_v_o(dec_retail_price_improvement_indicator_stock_locate_early_lite_v[i]),
			.itch_retail_price_improvement_indicator_tracking_number_early_lite_v_o(dec_retail_price_improvement_indicator_tracking_number_early_lite_v[i]),
			.itch_retail_price_improvement_indicator_timestamp_early_lite_v_o(dec_retail_price_improvement_indicator_timestamp_early_lite_v[i]),
			.itch_retail_price_improvement_indicator_stock_early_lite_v_o(dec_retail_price_improvement_indicator_stock_early_lite_v[i]),
			.itch_retail_price_improvement_indicator_interest_flag_early_lite_v_o(dec_retail_price_improvement_indicator_interest_flag_early_lite_v[i]),
			
			`ifdef GLIMPSE
			.itch_end_of_snapshot_early_v_o(dec_end_of_snapshot_early_v[i]),
			.itch_end_of_snapshot_sequence_number_early_lite_v_o(dec_end_of_snapshot_sequence_number_early_lite_v[i]),
			`endif // GLIMPSE
			`endif // EARLY
		
			.itch_system_event_v_o(dec_system_event_v[i]),
			.itch_system_event_stock_locate_o(dec_system_event_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_system_event_tracking_number_o(dec_system_event_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_system_event_timestamp_o(dec_system_event_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_system_event_event_code_o(dec_system_event_event_code[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_stock_directory_v_o(dec_stock_directory_v[i]),
			.itch_stock_directory_stock_locate_o(dec_stock_directory_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_stock_directory_tracking_number_o(dec_stock_directory_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_stock_directory_timestamp_o(dec_stock_directory_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_stock_directory_stock_o(dec_stock_directory_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_stock_directory_market_category_o(dec_stock_directory_market_category[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_financial_status_indicator_o(dec_stock_directory_financial_status_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_round_lot_size_o(dec_stock_directory_round_lot_size[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_stock_directory_round_lots_only_o(dec_stock_directory_round_lots_only[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_issue_classification_o(dec_stock_directory_issue_classification[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_issue_sub_type_o(dec_stock_directory_issue_sub_type[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_stock_directory_authenticity_o(dec_stock_directory_authenticity[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_short_sale_threshold_indicator_o(dec_stock_directory_short_sale_threshold_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_ipo_flag_o(dec_stock_directory_ipo_flag[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_luld_reference_price_tier_o(dec_stock_directory_luld_reference_price_tier[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_etp_flag_o(dec_stock_directory_etp_flag[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_directory_etp_leverage_factor_o(dec_stock_directory_etp_leverage_factor[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_stock_directory_inverse_indicator_o(dec_stock_directory_inverse_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_stock_trading_action_v_o(dec_stock_trading_action_v[i]),
			.itch_stock_trading_action_stock_locate_o(dec_stock_trading_action_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_stock_trading_action_tracking_number_o(dec_stock_trading_action_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_stock_trading_action_timestamp_o(dec_stock_trading_action_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_stock_trading_action_stock_o(dec_stock_trading_action_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_stock_trading_action_trading_state_o(dec_stock_trading_action_trading_state[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_trading_action_reserved_o(dec_stock_trading_action_reserved[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_stock_trading_action_reason_o(dec_stock_trading_action_reason[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_reg_sho_restriction_v_o(dec_reg_sho_restriction_v[i]),
			.itch_reg_sho_restriction_stock_locate_o(dec_reg_sho_restriction_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_reg_sho_restriction_tracking_number_o(dec_reg_sho_restriction_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_reg_sho_restriction_timestamp_o(dec_reg_sho_restriction_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_reg_sho_restriction_stock_o(dec_reg_sho_restriction_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_reg_sho_restriction_reg_sho_action_o(dec_reg_sho_restriction_reg_sho_action[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_market_participant_position_v_o(dec_market_participant_position_v[i]),
			.itch_market_participant_position_stock_locate_o(dec_market_participant_position_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_market_participant_position_tracking_number_o(dec_market_participant_position_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_market_participant_position_timestamp_o(dec_market_participant_position_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_market_participant_position_mpid_o(dec_market_participant_position_mpid[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_market_participant_position_stock_o(dec_market_participant_position_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_market_participant_position_primary_market_maker_o(dec_market_participant_position_primary_market_maker[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_market_participant_position_market_maker_mode_o(dec_market_participant_position_market_maker_mode[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_market_participant_position_market_participant_state_o(dec_market_participant_position_market_participant_state[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_mwcb_decline_level_v_o(dec_mwcb_decline_level_v[i]),
			.itch_mwcb_decline_level_stock_locate_o(dec_mwcb_decline_level_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_mwcb_decline_level_tracking_number_o(dec_mwcb_decline_level_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_mwcb_decline_level_timestamp_o(dec_mwcb_decline_level_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_mwcb_decline_level_level_1_o(dec_mwcb_decline_level_level_1[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_mwcb_decline_level_level_2_o(dec_mwcb_decline_level_level_2[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_mwcb_decline_level_level_3_o(dec_mwcb_decline_level_level_3[i*8*LEN+8*LEN-1:i*8*LEN]),
			
			.itch_mwcb_status_v_o(dec_mwcb_status_v[i]),
			.itch_mwcb_status_stock_locate_o(dec_mwcb_status_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_mwcb_status_tracking_number_o(dec_mwcb_status_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_mwcb_status_timestamp_o(dec_mwcb_status_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_mwcb_status_breached_level_o(dec_mwcb_status_breached_level[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_ipo_quoting_period_update_v_o(dec_ipo_quoting_period_update_v[i]),
			.itch_ipo_quoting_period_update_stock_locate_o(dec_ipo_quoting_period_update_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_ipo_quoting_period_update_tracking_number_o(dec_ipo_quoting_period_update_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_ipo_quoting_period_update_timestamp_o(dec_ipo_quoting_period_update_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_ipo_quoting_period_update_stock_o(dec_ipo_quoting_period_update_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_ipo_quoting_period_update_ipo_quotation_release_time_o(dec_ipo_quoting_period_update_ipo_quotation_release_time[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o(dec_ipo_quoting_period_update_ipo_quotation_release_qualifier[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_ipo_quoting_period_update_ipo_price_o(dec_ipo_quoting_period_update_ipo_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_luld_auction_collar_v_o(dec_luld_auction_collar_v[i]),
			.itch_luld_auction_collar_stock_locate_o(dec_luld_auction_collar_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_luld_auction_collar_tracking_number_o(dec_luld_auction_collar_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_luld_auction_collar_timestamp_o(dec_luld_auction_collar_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_luld_auction_collar_stock_o(dec_luld_auction_collar_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_luld_auction_collar_auction_collar_reference_price_o(dec_luld_auction_collar_auction_collar_reference_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_luld_auction_collar_upper_auction_collar_price_o(dec_luld_auction_collar_upper_auction_collar_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_luld_auction_collar_lower_auction_collar_price_o(dec_luld_auction_collar_lower_auction_collar_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_luld_auction_collar_auction_collar_extension_o(dec_luld_auction_collar_auction_collar_extension[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_operational_halt_v_o(dec_operational_halt_v[i]),
			.itch_operational_halt_stock_locate_o(dec_operational_halt_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_operational_halt_tracking_number_o(dec_operational_halt_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_operational_halt_timestamp_o(dec_operational_halt_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_operational_halt_stock_o(dec_operational_halt_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_operational_halt_market_code_o(dec_operational_halt_market_code[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_operational_halt_operational_halt_action_o(dec_operational_halt_operational_halt_action[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_add_order_v_o(dec_add_order_v[i]),
			.itch_add_order_stock_locate_o(dec_add_order_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_add_order_tracking_number_o(dec_add_order_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_add_order_timestamp_o(dec_add_order_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_add_order_order_reference_number_o(dec_add_order_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_add_order_buy_sell_indicator_o(dec_add_order_buy_sell_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_add_order_shares_o(dec_add_order_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_add_order_stock_o(dec_add_order_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_add_order_price_o(dec_add_order_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_add_order_with_mpid_v_o(dec_add_order_with_mpid_v[i]),
			.itch_add_order_with_mpid_stock_locate_o(dec_add_order_with_mpid_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_add_order_with_mpid_tracking_number_o(dec_add_order_with_mpid_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_add_order_with_mpid_timestamp_o(dec_add_order_with_mpid_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_add_order_with_mpid_order_reference_number_o(dec_add_order_with_mpid_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_add_order_with_mpid_buy_sell_indicator_o(dec_add_order_with_mpid_buy_sell_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_add_order_with_mpid_shares_o(dec_add_order_with_mpid_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_add_order_with_mpid_stock_o(dec_add_order_with_mpid_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_add_order_with_mpid_price_o(dec_add_order_with_mpid_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_add_order_with_mpid_attribution_o(dec_add_order_with_mpid_attribution[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_order_executed_v_o(dec_order_executed_v[i]),
			.itch_order_executed_stock_locate_o(dec_order_executed_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_executed_tracking_number_o(dec_order_executed_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_executed_timestamp_o(dec_order_executed_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_order_executed_order_reference_number_o(dec_order_executed_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_order_executed_executed_shares_o(dec_order_executed_executed_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_order_executed_match_number_o(dec_order_executed_match_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			
			.itch_order_executed_with_price_v_o(dec_order_executed_with_price_v[i]),
			.itch_order_executed_with_price_stock_locate_o(dec_order_executed_with_price_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_executed_with_price_tracking_number_o(dec_order_executed_with_price_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_executed_with_price_timestamp_o(dec_order_executed_with_price_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_order_executed_with_price_order_reference_number_o(dec_order_executed_with_price_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_order_executed_with_price_executed_shares_o(dec_order_executed_with_price_executed_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_order_executed_with_price_match_number_o(dec_order_executed_with_price_match_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_order_executed_with_price_printable_o(dec_order_executed_with_price_printable[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_order_executed_with_price_execution_price_o(dec_order_executed_with_price_execution_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_order_cancel_v_o(dec_order_cancel_v[i]),
			.itch_order_cancel_stock_locate_o(dec_order_cancel_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_cancel_tracking_number_o(dec_order_cancel_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_cancel_timestamp_o(dec_order_cancel_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_order_cancel_order_reference_number_o(dec_order_cancel_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_order_cancel_cancelled_shares_o(dec_order_cancel_cancelled_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_order_delete_v_o(dec_order_delete_v[i]),
			.itch_order_delete_stock_locate_o(dec_order_delete_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_delete_tracking_number_o(dec_order_delete_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_delete_timestamp_o(dec_order_delete_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_order_delete_order_reference_number_o(dec_order_delete_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			
			.itch_order_replace_v_o(dec_order_replace_v[i]),
			.itch_order_replace_stock_locate_o(dec_order_replace_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_replace_tracking_number_o(dec_order_replace_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_order_replace_timestamp_o(dec_order_replace_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_order_replace_original_order_reference_number_o(dec_order_replace_original_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_order_replace_new_order_reference_number_o(dec_order_replace_new_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_order_replace_shares_o(dec_order_replace_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_order_replace_price_o(dec_order_replace_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			
			.itch_trade_v_o(dec_trade_v[i]),
			.itch_trade_stock_locate_o(dec_trade_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_trade_tracking_number_o(dec_trade_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_trade_timestamp_o(dec_trade_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_trade_order_reference_number_o(dec_trade_order_reference_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_trade_buy_sell_indicator_o(dec_trade_buy_sell_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_trade_shares_o(dec_trade_shares[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_trade_stock_o(dec_trade_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_trade_price_o(dec_trade_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_trade_match_number_o(dec_trade_match_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			
			.itch_cross_trade_v_o(dec_cross_trade_v[i]),
			.itch_cross_trade_stock_locate_o(dec_cross_trade_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_cross_trade_tracking_number_o(dec_cross_trade_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_cross_trade_timestamp_o(dec_cross_trade_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_cross_trade_shares_o(dec_cross_trade_shares[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_cross_trade_stock_o(dec_cross_trade_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_cross_trade_cross_price_o(dec_cross_trade_cross_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_cross_trade_match_number_o(dec_cross_trade_match_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_cross_trade_cross_type_o(dec_cross_trade_cross_type[i*1*LEN+1*LEN-1:i*1*LEN]),
			
			.itch_broken_trade_v_o(dec_broken_trade_v[i]),
			.itch_broken_trade_stock_locate_o(dec_broken_trade_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_broken_trade_tracking_number_o(dec_broken_trade_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_broken_trade_timestamp_o(dec_broken_trade_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_broken_trade_match_number_o(dec_broken_trade_match_number[i*8*LEN+8*LEN-1:i*8*LEN]),
			
			.itch_net_order_imbalance_indicator_v_o(dec_net_order_imbalance_indicator_v[i]),
			.itch_net_order_imbalance_indicator_stock_locate_o(dec_net_order_imbalance_indicator_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_net_order_imbalance_indicator_tracking_number_o(dec_net_order_imbalance_indicator_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_net_order_imbalance_indicator_timestamp_o(dec_net_order_imbalance_indicator_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_net_order_imbalance_indicator_paired_shares_o(dec_net_order_imbalance_indicator_paired_shares[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_net_order_imbalance_indicator_imbalance_shares_o(dec_net_order_imbalance_indicator_imbalance_shares[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_net_order_imbalance_indicator_imbalance_direction_o(dec_net_order_imbalance_indicator_imbalance_direction[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_net_order_imbalance_indicator_stock_o(dec_net_order_imbalance_indicator_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_net_order_imbalance_indicator_far_price_o(dec_net_order_imbalance_indicator_far_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_net_order_imbalance_indicator_near_price_o(dec_net_order_imbalance_indicator_near_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_net_order_imbalance_indicator_current_reference_price_o(dec_net_order_imbalance_indicator_current_reference_price[i*4*LEN+4*LEN-1:i*4*LEN]),
			.itch_net_order_imbalance_indicator_cross_type_o(dec_net_order_imbalance_indicator_cross_type[i*1*LEN+1*LEN-1:i*1*LEN]),
			.itch_net_order_imbalance_indicator_price_variation_indicator_o(dec_net_order_imbalance_indicator_price_variation_indicator[i*1*LEN+1*LEN-1:i*1*LEN]),
	
			`ifdef GLIMPSE	
			.itch_end_of_snapshot_v_o(dec_end_of_snapshot_v[i]),
			.itch_end_of_snapshot_sequence_number_o(dec_end_of_snapshot_sequence_number[i*20*LEN+20*LEN-1:i*20*LEN]),		
			`endif

			.itch_retail_price_improvement_indicator_v_o(dec_retail_price_improvement_indicator_v[i]),
			.itch_retail_price_improvement_indicator_stock_locate_o(dec_retail_price_improvement_indicator_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_retail_price_improvement_indicator_tracking_number_o(dec_retail_price_improvement_indicator_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
			.itch_retail_price_improvement_indicator_timestamp_o(dec_retail_price_improvement_indicator_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
			.itch_retail_price_improvement_indicator_stock_o(dec_retail_price_improvement_indicator_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
			.itch_retail_price_improvement_indicator_interest_flag_o(dec_retail_price_improvement_indicator_interest_flag[i*1*LEN+1*LEN-1:i*1*LEN])
			);
	end
endgenerate

// mux

tv_itch5_mux #(.LEN(LEN), .ITCH_N(ITCH_N) ) m_itch_mux (
.dec_system_event_v_i(dec_system_event_v),
.dec_system_event_stock_locate_i(dec_system_event_stock_locate),
.dec_system_event_tracking_number_i(dec_system_event_tracking_number),
.dec_system_event_timestamp_i(dec_system_event_timestamp),
.dec_system_event_event_code_i(dec_system_event_event_code),
	
.dec_stock_directory_v_i(dec_stock_directory_v),
.dec_stock_directory_stock_locate_i(dec_stock_directory_stock_locate),
.dec_stock_directory_tracking_number_i(dec_stock_directory_tracking_number),
.dec_stock_directory_timestamp_i(dec_stock_directory_timestamp),
.dec_stock_directory_stock_i(dec_stock_directory_stock),
.dec_stock_directory_market_category_i(dec_stock_directory_market_category),
.dec_stock_directory_financial_status_indicator_i(dec_stock_directory_financial_status_indicator),
.dec_stock_directory_round_lot_size_i(dec_stock_directory_round_lot_size),
.dec_stock_directory_round_lots_only_i(dec_stock_directory_round_lots_only),
.dec_stock_directory_issue_classification_i(dec_stock_directory_issue_classification),
.dec_stock_directory_issue_sub_type_i(dec_stock_directory_issue_sub_type),
.dec_stock_directory_authenticity_i(dec_stock_directory_authenticity),
.dec_stock_directory_short_sale_threshold_indicator_i(dec_stock_directory_short_sale_threshold_indicator),
.dec_stock_directory_ipo_flag_i(dec_stock_directory_ipo_flag),
.dec_stock_directory_luld_reference_price_tier_i(dec_stock_directory_luld_reference_price_tier),
.dec_stock_directory_etp_flag_i(dec_stock_directory_etp_flag),
.dec_stock_directory_etp_leverage_factor_i(dec_stock_directory_etp_leverage_factor),
.dec_stock_directory_inverse_indicator_i(dec_stock_directory_inverse_indicator),
	
.dec_stock_trading_action_v_i(dec_stock_trading_action_v),
.dec_stock_trading_action_stock_locate_i(dec_stock_trading_action_stock_locate),
.dec_stock_trading_action_tracking_number_i(dec_stock_trading_action_tracking_number),
.dec_stock_trading_action_timestamp_i(dec_stock_trading_action_timestamp),
.dec_stock_trading_action_stock_i(dec_stock_trading_action_stock),
.dec_stock_trading_action_trading_state_i(dec_stock_trading_action_trading_state),
.dec_stock_trading_action_reserved_i(dec_stock_trading_action_reserved),
.dec_stock_trading_action_reason_i(dec_stock_trading_action_reason),
	
.dec_reg_sho_restriction_v_i(dec_reg_sho_restriction_v),
.dec_reg_sho_restriction_stock_locate_i(dec_reg_sho_restriction_stock_locate),
.dec_reg_sho_restriction_tracking_number_i(dec_reg_sho_restriction_tracking_number),
.dec_reg_sho_restriction_timestamp_i(dec_reg_sho_restriction_timestamp),
.dec_reg_sho_restriction_stock_i(dec_reg_sho_restriction_stock),
.dec_reg_sho_restriction_reg_sho_action_i(dec_reg_sho_restriction_reg_sho_action),
	
.dec_market_participant_position_v_i(dec_market_participant_position_v),
.dec_market_participant_position_stock_locate_i(dec_market_participant_position_stock_locate),
.dec_market_participant_position_tracking_number_i(dec_market_participant_position_tracking_number),
.dec_market_participant_position_timestamp_i(dec_market_participant_position_timestamp),
.dec_market_participant_position_mpid_i(dec_market_participant_position_mpid),
.dec_market_participant_position_stock_i(dec_market_participant_position_stock),
.dec_market_participant_position_primary_market_maker_i(dec_market_participant_position_primary_market_maker),
.dec_market_participant_position_market_maker_mode_i(dec_market_participant_position_market_maker_mode),
.dec_market_participant_position_market_participant_state_i(dec_market_participant_position_market_participant_state),
	
.dec_mwcb_decline_level_v_i(dec_mwcb_decline_level_v),
.dec_mwcb_decline_level_stock_locate_i(dec_mwcb_decline_level_stock_locate),
.dec_mwcb_decline_level_tracking_number_i(dec_mwcb_decline_level_tracking_number),
.dec_mwcb_decline_level_timestamp_i(dec_mwcb_decline_level_timestamp),
.dec_mwcb_decline_level_level_1_i(dec_mwcb_decline_level_level_1),
.dec_mwcb_decline_level_level_2_i(dec_mwcb_decline_level_level_2),
.dec_mwcb_decline_level_level_3_i(dec_mwcb_decline_level_level_3),
	
.dec_mwcb_status_v_i(dec_mwcb_status_v),
.dec_mwcb_status_stock_locate_i(dec_mwcb_status_stock_locate),
.dec_mwcb_status_tracking_number_i(dec_mwcb_status_tracking_number),
.dec_mwcb_status_timestamp_i(dec_mwcb_status_timestamp),
.dec_mwcb_status_breached_level_i(dec_mwcb_status_breached_level),
	
.dec_ipo_quoting_period_update_v_i(dec_ipo_quoting_period_update_v),
.dec_ipo_quoting_period_update_stock_locate_i(dec_ipo_quoting_period_update_stock_locate),
.dec_ipo_quoting_period_update_tracking_number_i(dec_ipo_quoting_period_update_tracking_number),
.dec_ipo_quoting_period_update_timestamp_i(dec_ipo_quoting_period_update_timestamp),
.dec_ipo_quoting_period_update_stock_i(dec_ipo_quoting_period_update_stock),
.dec_ipo_quoting_period_update_ipo_quotation_release_time_i(dec_ipo_quoting_period_update_ipo_quotation_release_time),
.dec_ipo_quoting_period_update_ipo_quotation_release_qualifier_i(dec_ipo_quoting_period_update_ipo_quotation_release_qualifier),
.dec_ipo_quoting_period_update_ipo_price_i(dec_ipo_quoting_period_update_ipo_price),
	
.dec_luld_auction_collar_v_i(dec_luld_auction_collar_v),
.dec_luld_auction_collar_stock_locate_i(dec_luld_auction_collar_stock_locate),
.dec_luld_auction_collar_tracking_number_i(dec_luld_auction_collar_tracking_number),
.dec_luld_auction_collar_timestamp_i(dec_luld_auction_collar_timestamp),
.dec_luld_auction_collar_stock_i(dec_luld_auction_collar_stock),
.dec_luld_auction_collar_auction_collar_reference_price_i(dec_luld_auction_collar_auction_collar_reference_price),
.dec_luld_auction_collar_upper_auction_collar_price_i(dec_luld_auction_collar_upper_auction_collar_price),
.dec_luld_auction_collar_lower_auction_collar_price_i(dec_luld_auction_collar_lower_auction_collar_price),
.dec_luld_auction_collar_auction_collar_extension_i(dec_luld_auction_collar_auction_collar_extension),
	
.dec_operational_halt_v_i(dec_operational_halt_v),
.dec_operational_halt_stock_locate_i(dec_operational_halt_stock_locate),
.dec_operational_halt_tracking_number_i(dec_operational_halt_tracking_number),
.dec_operational_halt_timestamp_i(dec_operational_halt_timestamp),
.dec_operational_halt_stock_i(dec_operational_halt_stock),
.dec_operational_halt_market_code_i(dec_operational_halt_market_code),
.dec_operational_halt_operational_halt_action_i(dec_operational_halt_operational_halt_action),
	
.dec_add_order_v_i(dec_add_order_v),
.dec_add_order_stock_locate_i(dec_add_order_stock_locate),
.dec_add_order_tracking_number_i(dec_add_order_tracking_number),
.dec_add_order_timestamp_i(dec_add_order_timestamp),
.dec_add_order_order_reference_number_i(dec_add_order_order_reference_number),
.dec_add_order_buy_sell_indicator_i(dec_add_order_buy_sell_indicator),
.dec_add_order_shares_i(dec_add_order_shares),
.dec_add_order_stock_i(dec_add_order_stock),
.dec_add_order_price_i(dec_add_order_price),
	
.dec_add_order_with_mpid_v_i(dec_add_order_with_mpid_v),
.dec_add_order_with_mpid_stock_locate_i(dec_add_order_with_mpid_stock_locate),
.dec_add_order_with_mpid_tracking_number_i(dec_add_order_with_mpid_tracking_number),
.dec_add_order_with_mpid_timestamp_i(dec_add_order_with_mpid_timestamp),
.dec_add_order_with_mpid_order_reference_number_i(dec_add_order_with_mpid_order_reference_number),
.dec_add_order_with_mpid_buy_sell_indicator_i(dec_add_order_with_mpid_buy_sell_indicator),
.dec_add_order_with_mpid_shares_i(dec_add_order_with_mpid_shares),
.dec_add_order_with_mpid_stock_i(dec_add_order_with_mpid_stock),
.dec_add_order_with_mpid_price_i(dec_add_order_with_mpid_price),
.dec_add_order_with_mpid_attribution_i(dec_add_order_with_mpid_attribution),
	
.dec_order_executed_v_i(dec_order_executed_v),
.dec_order_executed_stock_locate_i(dec_order_executed_stock_locate),
.dec_order_executed_tracking_number_i(dec_order_executed_tracking_number),
.dec_order_executed_timestamp_i(dec_order_executed_timestamp),
.dec_order_executed_order_reference_number_i(dec_order_executed_order_reference_number),
.dec_order_executed_executed_shares_i(dec_order_executed_executed_shares),
.dec_order_executed_match_number_i(dec_order_executed_match_number),
	
.dec_order_executed_with_price_v_i(dec_order_executed_with_price_v),
.dec_order_executed_with_price_stock_locate_i(dec_order_executed_with_price_stock_locate),
.dec_order_executed_with_price_tracking_number_i(dec_order_executed_with_price_tracking_number),
.dec_order_executed_with_price_timestamp_i(dec_order_executed_with_price_timestamp),
.dec_order_executed_with_price_order_reference_number_i(dec_order_executed_with_price_order_reference_number),
.dec_order_executed_with_price_executed_shares_i(dec_order_executed_with_price_executed_shares),
.dec_order_executed_with_price_match_number_i(dec_order_executed_with_price_match_number),
.dec_order_executed_with_price_printable_i(dec_order_executed_with_price_printable),
.dec_order_executed_with_price_execution_price_i(dec_order_executed_with_price_execution_price),
	
.dec_order_cancel_v_i(dec_order_cancel_v),
.dec_order_cancel_stock_locate_i(dec_order_cancel_stock_locate),
.dec_order_cancel_tracking_number_i(dec_order_cancel_tracking_number),
.dec_order_cancel_timestamp_i(dec_order_cancel_timestamp),
.dec_order_cancel_order_reference_number_i(dec_order_cancel_order_reference_number),
.dec_order_cancel_cancelled_shares_i(dec_order_cancel_cancelled_shares),
	
.dec_order_delete_v_i(dec_order_delete_v),
.dec_order_delete_stock_locate_i(dec_order_delete_stock_locate),
.dec_order_delete_tracking_number_i(dec_order_delete_tracking_number),
.dec_order_delete_timestamp_i(dec_order_delete_timestamp),
.dec_order_delete_order_reference_number_i(dec_order_delete_order_reference_number),
	
.dec_order_replace_v_i(dec_order_replace_v),
.dec_order_replace_stock_locate_i(dec_order_replace_stock_locate),
.dec_order_replace_tracking_number_i(dec_order_replace_tracking_number),
.dec_order_replace_timestamp_i(dec_order_replace_timestamp),
.dec_order_replace_original_order_reference_number_i(dec_order_replace_original_order_reference_number),
.dec_order_replace_new_order_reference_number_i(dec_order_replace_new_order_reference_number),
.dec_order_replace_shares_i(dec_order_replace_shares),
.dec_order_replace_price_i(dec_order_replace_price),
	
.dec_trade_v_i(dec_trade_v),
.dec_trade_stock_locate_i(dec_trade_stock_locate),
.dec_trade_tracking_number_i(dec_trade_tracking_number),
.dec_trade_timestamp_i(dec_trade_timestamp),
.dec_trade_order_reference_number_i(dec_trade_order_reference_number),
.dec_trade_buy_sell_indicator_i(dec_trade_buy_sell_indicator),
.dec_trade_shares_i(dec_trade_shares),
.dec_trade_stock_i(dec_trade_stock),
.dec_trade_price_i(dec_trade_price),
.dec_trade_match_number_i(dec_trade_match_number),
	
.dec_cross_trade_v_i(dec_cross_trade_v),
.dec_cross_trade_stock_locate_i(dec_cross_trade_stock_locate),
.dec_cross_trade_tracking_number_i(dec_cross_trade_tracking_number),
.dec_cross_trade_timestamp_i(dec_cross_trade_timestamp),
.dec_cross_trade_shares_i(dec_cross_trade_shares),
.dec_cross_trade_stock_i(dec_cross_trade_stock),
.dec_cross_trade_cross_price_i(dec_cross_trade_cross_price),
.dec_cross_trade_match_number_i(dec_cross_trade_match_number),
.dec_cross_trade_cross_type_i(dec_cross_trade_cross_type),
	
.dec_broken_trade_v_i(dec_broken_trade_v),
.dec_broken_trade_stock_locate_i(dec_broken_trade_stock_locate),
.dec_broken_trade_tracking_number_i(dec_broken_trade_tracking_number),
.dec_broken_trade_timestamp_i(dec_broken_trade_timestamp),
.dec_broken_trade_match_number_i(dec_broken_trade_match_number),
	
.dec_net_order_imbalance_indicator_v_i(dec_net_order_imbalance_indicator_v),
.dec_net_order_imbalance_indicator_stock_locate_i(dec_net_order_imbalance_indicator_stock_locate),
.dec_net_order_imbalance_indicator_tracking_number_i(dec_net_order_imbalance_indicator_tracking_number),
.dec_net_order_imbalance_indicator_timestamp_i(dec_net_order_imbalance_indicator_timestamp),
.dec_net_order_imbalance_indicator_paired_shares_i(dec_net_order_imbalance_indicator_paired_shares),
.dec_net_order_imbalance_indicator_imbalance_shares_i(dec_net_order_imbalance_indicator_imbalance_shares),
.dec_net_order_imbalance_indicator_imbalance_direction_i(dec_net_order_imbalance_indicator_imbalance_direction),
.dec_net_order_imbalance_indicator_stock_i(dec_net_order_imbalance_indicator_stock),
.dec_net_order_imbalance_indicator_far_price_i(dec_net_order_imbalance_indicator_far_price),
.dec_net_order_imbalance_indicator_near_price_i(dec_net_order_imbalance_indicator_near_price),
.dec_net_order_imbalance_indicator_current_reference_price_i(dec_net_order_imbalance_indicator_current_reference_price),
.dec_net_order_imbalance_indicator_cross_type_i(dec_net_order_imbalance_indicator_cross_type),
.dec_net_order_imbalance_indicator_price_variation_indicator_i(dec_net_order_imbalance_indicator_price_variation_indicator),
	
	`ifdef GLIMPSE
.dec_end_of_snapshot_v_i(dec_end_of_snapshot_v),
.dec_end_of_snapshot_sequence_number_i(dec_end_of_snapshot_sequence_number),
	`endif
	
.dec_retail_price_improvement_indicator_v_i(dec_retail_price_improvement_indicator_v),
.dec_retail_price_improvement_indicator_stock_locate_i(dec_retail_price_improvement_indicator_stock_locate),
.dec_retail_price_improvement_indicator_tracking_number_i(dec_retail_price_improvement_indicator_tracking_number),
.dec_retail_price_improvement_indicator_timestamp_i(dec_retail_price_improvement_indicator_timestamp),
.dec_retail_price_improvement_indicator_stock_i(dec_retail_price_improvement_indicator_stock),
.dec_retail_price_improvement_indicator_interest_flag_i(dec_retail_price_improvement_indicator_interest_flag),

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
