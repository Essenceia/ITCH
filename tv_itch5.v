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
`ifdef EARLY
logic  dec_system_event_early_v[ITCH_N-1:0];
logic  dec_system_event_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_system_event_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_system_event_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_system_event_event_code_early_lite_v[ITCH_N-1:0];

logic  dec_stock_directory_early_v[ITCH_N-1:0];
logic  dec_stock_directory_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_stock_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_market_category_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_financial_status_indicator_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_round_lot_size_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_round_lots_only_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_issue_classification_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_issue_sub_type_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_authenticity_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_short_sale_threshold_indicator_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_ipo_flag_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_luld_reference_price_tier_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_etp_flag_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_etp_leverage_factor_early_lite_v[ITCH_N-1:0];
logic  dec_stock_directory_inverse_indicator_early_lite_v[ITCH_N-1:0];

logic  dec_stock_trading_action_early_v[ITCH_N-1:0];
logic  dec_stock_trading_action_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_stock_trading_action_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_stock_trading_action_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_stock_trading_action_stock_early_lite_v[ITCH_N-1:0];
logic  dec_stock_trading_action_trading_state_early_lite_v[ITCH_N-1:0];
logic  dec_stock_trading_action_reserved_early_lite_v[ITCH_N-1:0];
logic  dec_stock_trading_action_reason_early_lite_v[ITCH_N-1:0];

logic  dec_reg_sho_restriction_early_v[ITCH_N-1:0];
logic  dec_reg_sho_restriction_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_reg_sho_restriction_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_reg_sho_restriction_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_reg_sho_restriction_stock_early_lite_v[ITCH_N-1:0];
logic  dec_reg_sho_restriction_reg_sho_action_early_lite_v[ITCH_N-1:0];

logic  dec_market_participant_position_early_v[ITCH_N-1:0];
logic  dec_market_participant_position_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_mpid_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_stock_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_primary_market_maker_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_market_maker_mode_early_lite_v[ITCH_N-1:0];
logic  dec_market_participant_position_market_participant_state_early_lite_v[ITCH_N-1:0];

logic  dec_mwcb_decline_level_early_v[ITCH_N-1:0];
logic  dec_mwcb_decline_level_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_decline_level_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_decline_level_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_decline_level_level_1_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_decline_level_level_2_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_decline_level_level_3_early_lite_v[ITCH_N-1:0];

logic  dec_mwcb_status_early_v[ITCH_N-1:0];
logic  dec_mwcb_status_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_status_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_status_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_mwcb_status_breached_level_early_lite_v[ITCH_N-1:0];

logic  dec_ipo_quoting_period_update_early_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_stock_early_lite_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_ipo_quotation_release_time_early_lite_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_ipo_quotation_release_qualifier_early_lite_v[ITCH_N-1:0];
logic  dec_ipo_quoting_period_update_ipo_price_early_lite_v[ITCH_N-1:0];

logic  dec_luld_auction_collar_early_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_stock_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_auction_collar_reference_price_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_upper_auction_collar_price_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_lower_auction_collar_price_early_lite_v[ITCH_N-1:0];
logic  dec_luld_auction_collar_auction_collar_extension_early_lite_v[ITCH_N-1:0];

logic  dec_operational_halt_early_v[ITCH_N-1:0];
logic  dec_operational_halt_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_operational_halt_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_operational_halt_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_operational_halt_stock_early_lite_v[ITCH_N-1:0];
logic  dec_operational_halt_market_code_early_lite_v[ITCH_N-1:0];
logic  dec_operational_halt_operational_halt_action_early_lite_v[ITCH_N-1:0];

logic  dec_add_order_early_v[ITCH_N-1:0];
logic  dec_add_order_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_buy_sell_indicator_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_shares_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_stock_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_price_early_lite_v[ITCH_N-1:0];

logic  dec_add_order_with_mpid_early_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_buy_sell_indicator_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_shares_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_stock_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_price_early_lite_v[ITCH_N-1:0];
logic  dec_add_order_with_mpid_attribution_early_lite_v[ITCH_N-1:0];

logic  dec_order_executed_early_v[ITCH_N-1:0];
logic  dec_order_executed_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_executed_shares_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_match_number_early_lite_v[ITCH_N-1:0];

logic  dec_order_executed_with_price_early_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_executed_shares_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_match_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_printable_early_lite_v[ITCH_N-1:0];
logic  dec_order_executed_with_price_execution_price_early_lite_v[ITCH_N-1:0];

logic  dec_order_cancel_early_v[ITCH_N-1:0];
logic  dec_order_cancel_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_order_cancel_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_cancel_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_order_cancel_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_cancel_cancelled_shares_early_lite_v[ITCH_N-1:0];

logic  dec_order_delete_early_v[ITCH_N-1:0];
logic  dec_order_delete_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_order_delete_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_delete_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_order_delete_order_reference_number_early_lite_v[ITCH_N-1:0];

logic  dec_order_replace_early_v[ITCH_N-1:0];
logic  dec_order_replace_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_order_replace_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_replace_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_order_replace_original_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_replace_new_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_order_replace_shares_early_lite_v[ITCH_N-1:0];
logic  dec_order_replace_price_early_lite_v[ITCH_N-1:0];

logic  dec_trade_early_v[ITCH_N-1:0];
logic  dec_trade_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_trade_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_trade_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_trade_order_reference_number_early_lite_v[ITCH_N-1:0];
logic  dec_trade_buy_sell_indicator_early_lite_v[ITCH_N-1:0];
logic  dec_trade_shares_early_lite_v[ITCH_N-1:0];
logic  dec_trade_stock_early_lite_v[ITCH_N-1:0];
logic  dec_trade_price_early_lite_v[ITCH_N-1:0];
logic  dec_trade_match_number_early_lite_v[ITCH_N-1:0];

logic  dec_cross_trade_early_v[ITCH_N-1:0];
logic  dec_cross_trade_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_shares_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_stock_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_cross_price_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_match_number_early_lite_v[ITCH_N-1:0];
logic  dec_cross_trade_cross_type_early_lite_v[ITCH_N-1:0];

logic  dec_broken_trade_early_v[ITCH_N-1:0];
logic  dec_broken_trade_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_broken_trade_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_broken_trade_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_broken_trade_match_number_early_lite_v[ITCH_N-1:0];

logic  dec_net_order_imbalance_indicator_early_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_paired_shares_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_imbalance_shares_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_imbalance_direction_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_stock_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_far_price_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_near_price_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_current_reference_price_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_cross_type_early_lite_v[ITCH_N-1:0];
logic  dec_net_order_imbalance_indicator_price_variation_indicator_early_lite_v[ITCH_N-1:0];

logic  dec_retail_price_improvement_indicator_early_v[ITCH_N-1:0];
logic  dec_retail_price_improvement_indicator_stock_locate_early_lite_v[ITCH_N-1:0];
logic  dec_retail_price_improvement_indicator_tracking_number_early_lite_v[ITCH_N-1:0];
logic  dec_retail_price_improvement_indicator_timestamp_early_lite_v[ITCH_N-1:0];
logic  dec_retail_price_improvement_indicator_stock_early_lite_v[ITCH_N-1:0];
logic  dec_retail_price_improvement_indicator_interest_flag_early_lite_v[ITCH_N-1:0];

`ifdef GLIMPSE
logic  dec_end_of_snapshot_early_v[ITCH_N-1:0];
logic  dec_end_of_snapshot_sequence_number_early_lite_v[ITCH_N-1:0];
`endif // GLIMPSE
`endif // EARLY

logic  dec_system_event_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_system_event_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_system_event_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_system_event_timestamp[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_system_event_event_code[ITCH_N-1:0];

logic  dec_stock_directory_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_stock_directory_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_stock_directory_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_stock_directory_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_stock_directory_stock[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_market_category[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_financial_status_indicator[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_stock_directory_round_lot_size[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_round_lots_only[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_issue_classification[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_stock_directory_issue_sub_type[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_authenticity[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_short_sale_threshold_indicator[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_ipo_flag[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_luld_reference_price_tier[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_etp_flag[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_stock_directory_etp_leverage_factor[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_directory_inverse_indicator[ITCH_N-1:0];

logic  dec_stock_trading_action_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_stock_trading_action_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_stock_trading_action_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_stock_trading_action_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_stock_trading_action_stock[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_trading_action_trading_state[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_stock_trading_action_reserved[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_stock_trading_action_reason[ITCH_N-1:0];

logic  dec_reg_sho_restriction_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_reg_sho_restriction_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_reg_sho_restriction_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_reg_sho_restriction_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_reg_sho_restriction_stock[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_reg_sho_restriction_reg_sho_action[ITCH_N-1:0];

logic  dec_market_participant_position_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_market_participant_position_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_market_participant_position_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_market_participant_position_timestamp[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_market_participant_position_mpid[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_market_participant_position_stock[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_market_participant_position_primary_market_maker[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_market_participant_position_market_maker_mode[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_market_participant_position_market_participant_state[ITCH_N-1:0];

logic  dec_mwcb_decline_level_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_mwcb_decline_level_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_mwcb_decline_level_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_mwcb_decline_level_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_mwcb_decline_level_level_1[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_mwcb_decline_level_level_2[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_mwcb_decline_level_level_3[ITCH_N-1:0];

logic  dec_mwcb_status_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_mwcb_status_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_mwcb_status_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_mwcb_status_timestamp[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_mwcb_status_breached_level[ITCH_N-1:0];

logic  dec_ipo_quoting_period_update_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_ipo_quoting_period_update_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_ipo_quoting_period_update_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_ipo_quoting_period_update_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_ipo_quoting_period_update_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_ipo_quoting_period_update_ipo_quotation_release_time[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_ipo_quoting_period_update_ipo_quotation_release_qualifier[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_ipo_quoting_period_update_ipo_price[ITCH_N-1:0];

logic  dec_luld_auction_collar_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_luld_auction_collar_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_luld_auction_collar_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_luld_auction_collar_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_luld_auction_collar_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_luld_auction_collar_auction_collar_reference_price[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_luld_auction_collar_upper_auction_collar_price[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_luld_auction_collar_lower_auction_collar_price[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_luld_auction_collar_auction_collar_extension[ITCH_N-1:0];

logic  dec_operational_halt_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_operational_halt_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_operational_halt_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_operational_halt_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_operational_halt_stock[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_operational_halt_market_code[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_operational_halt_operational_halt_action[ITCH_N-1:0];

logic  dec_add_order_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_add_order_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_add_order_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_add_order_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_add_order_order_reference_number[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_add_order_buy_sell_indicator[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_add_order_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_add_order_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_add_order_price[ITCH_N-1:0];

logic  dec_add_order_with_mpid_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_add_order_with_mpid_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_add_order_with_mpid_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_add_order_with_mpid_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_add_order_with_mpid_order_reference_number[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_add_order_with_mpid_buy_sell_indicator[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_add_order_with_mpid_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_add_order_with_mpid_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_add_order_with_mpid_price[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_add_order_with_mpid_attribution[ITCH_N-1:0];

logic  dec_order_executed_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_executed_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_executed_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_order_executed_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_executed_order_reference_number[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_order_executed_executed_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_executed_match_number[ITCH_N-1:0];

logic  dec_order_executed_with_price_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_executed_with_price_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_executed_with_price_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_order_executed_with_price_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_executed_with_price_order_reference_number[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_order_executed_with_price_executed_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_executed_with_price_match_number[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_order_executed_with_price_printable[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_order_executed_with_price_execution_price[ITCH_N-1:0];

logic  dec_order_cancel_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_cancel_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_cancel_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_order_cancel_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_cancel_order_reference_number[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_order_cancel_cancelled_shares[ITCH_N-1:0];

logic  dec_order_delete_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_delete_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_delete_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_order_delete_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_delete_order_reference_number[ITCH_N-1:0];

logic  dec_order_replace_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_replace_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_order_replace_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_order_replace_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_replace_original_order_reference_number[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_order_replace_new_order_reference_number[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_order_replace_shares[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_order_replace_price[ITCH_N-1:0];

logic  dec_trade_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_trade_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_trade_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_trade_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_trade_order_reference_number[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_trade_buy_sell_indicator[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_trade_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_trade_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_trade_price[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_trade_match_number[ITCH_N-1:0];

logic  dec_cross_trade_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_cross_trade_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_cross_trade_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_cross_trade_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_cross_trade_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_cross_trade_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_cross_trade_cross_price[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_cross_trade_match_number[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_cross_trade_cross_type[ITCH_N-1:0];

logic  dec_broken_trade_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_broken_trade_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_broken_trade_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_broken_trade_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_broken_trade_match_number[ITCH_N-1:0];

logic  dec_net_order_imbalance_indicator_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_net_order_imbalance_indicator_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_net_order_imbalance_indicator_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_net_order_imbalance_indicator_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_net_order_imbalance_indicator_paired_shares[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_net_order_imbalance_indicator_imbalance_shares[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_net_order_imbalance_indicator_imbalance_direction[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_net_order_imbalance_indicator_stock[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_net_order_imbalance_indicator_far_price[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_net_order_imbalance_indicator_near_price[ITCH_N-1:0];
logic  [4*LEN-1:0] dec_net_order_imbalance_indicator_current_reference_price[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_net_order_imbalance_indicator_cross_type[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_net_order_imbalance_indicator_price_variation_indicator[ITCH_N-1:0];

`ifdef GLIMPSE
logic  dec_end_of_snapshot_v[ITCH_N-1:0];
logic  [20*LEN-1:0] dec_end_of_snapshot_sequence_number[ITCH_N-1:0];
`endif

logic  dec_retail_price_improvement_indicator_v[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_retail_price_improvement_indicator_stock_locate[ITCH_N-1:0];
logic  [2*LEN-1:0] dec_retail_price_improvement_indicator_tracking_number[ITCH_N-1:0];
logic  [6*LEN-1:0] dec_retail_price_improvement_indicator_timestamp[ITCH_N-1:0];
logic  [8*LEN-1:0] dec_retail_price_improvement_indicator_stock[ITCH_N-1:0];
logic  [1*LEN-1:0] dec_retail_price_improvement_indicator_interest_flag[ITCH_N-1:0];

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
			.itch_system_event_stock_locate_o(dec_system_event_stock_locate[i]),
			.itch_system_event_tracking_number_o(dec_system_event_tracking_number[i]),
			.itch_system_event_timestamp_o(dec_system_event_timestamp[i]),
			.itch_system_event_event_code_o(dec_system_event_event_code[i]),
			
			.itch_stock_directory_v_o(dec_stock_directory_v[i]),
			.itch_stock_directory_stock_locate_o(dec_stock_directory_stock_locate[i]),
			.itch_stock_directory_tracking_number_o(dec_stock_directory_tracking_number[i]),
			.itch_stock_directory_timestamp_o(dec_stock_directory_timestamp[i]),
			.itch_stock_directory_stock_o(dec_stock_directory_stock[i]),
			.itch_stock_directory_market_category_o(dec_stock_directory_market_category[i]),
			.itch_stock_directory_financial_status_indicator_o(dec_stock_directory_financial_status_indicator[i]),
			.itch_stock_directory_round_lot_size_o(dec_stock_directory_round_lot_size[i]),
			.itch_stock_directory_round_lots_only_o(dec_stock_directory_round_lots_only[i]),
			.itch_stock_directory_issue_classification_o(dec_stock_directory_issue_classification[i]),
			.itch_stock_directory_issue_sub_type_o(dec_stock_directory_issue_sub_type[i]),
			.itch_stock_directory_authenticity_o(dec_stock_directory_authenticity[i]),
			.itch_stock_directory_short_sale_threshold_indicator_o(dec_stock_directory_short_sale_threshold_indicator[i]),
			.itch_stock_directory_ipo_flag_o(dec_stock_directory_ipo_flag[i]),
			.itch_stock_directory_luld_reference_price_tier_o(dec_stock_directory_luld_reference_price_tier[i]),
			.itch_stock_directory_etp_flag_o(dec_stock_directory_etp_flag[i]),
			.itch_stock_directory_etp_leverage_factor_o(dec_stock_directory_etp_leverage_factor[i]),
			.itch_stock_directory_inverse_indicator_o(dec_stock_directory_inverse_indicator[i]),
			
			.itch_stock_trading_action_v_o(dec_stock_trading_action_v[i]),
			.itch_stock_trading_action_stock_locate_o(dec_stock_trading_action_stock_locate[i]),
			.itch_stock_trading_action_tracking_number_o(dec_stock_trading_action_tracking_number[i]),
			.itch_stock_trading_action_timestamp_o(dec_stock_trading_action_timestamp[i]),
			.itch_stock_trading_action_stock_o(dec_stock_trading_action_stock[i]),
			.itch_stock_trading_action_trading_state_o(dec_stock_trading_action_trading_state[i]),
			.itch_stock_trading_action_reserved_o(dec_stock_trading_action_reserved[i]),
			.itch_stock_trading_action_reason_o(dec_stock_trading_action_reason[i]),
			
			.itch_reg_sho_restriction_v_o(dec_reg_sho_restriction_v[i]),
			.itch_reg_sho_restriction_stock_locate_o(dec_reg_sho_restriction_stock_locate[i]),
			.itch_reg_sho_restriction_tracking_number_o(dec_reg_sho_restriction_tracking_number[i]),
			.itch_reg_sho_restriction_timestamp_o(dec_reg_sho_restriction_timestamp[i]),
			.itch_reg_sho_restriction_stock_o(dec_reg_sho_restriction_stock[i]),
			.itch_reg_sho_restriction_reg_sho_action_o(dec_reg_sho_restriction_reg_sho_action[i]),
			
			.itch_market_participant_position_v_o(dec_market_participant_position_v[i]),
			.itch_market_participant_position_stock_locate_o(dec_market_participant_position_stock_locate[i]),
			.itch_market_participant_position_tracking_number_o(dec_market_participant_position_tracking_number[i]),
			.itch_market_participant_position_timestamp_o(dec_market_participant_position_timestamp[i]),
			.itch_market_participant_position_mpid_o(dec_market_participant_position_mpid[i]),
			.itch_market_participant_position_stock_o(dec_market_participant_position_stock[i]),
			.itch_market_participant_position_primary_market_maker_o(dec_market_participant_position_primary_market_maker[i]),
			.itch_market_participant_position_market_maker_mode_o(dec_market_participant_position_market_maker_mode[i]),
			.itch_market_participant_position_market_participant_state_o(dec_market_participant_position_market_participant_state[i]),
			
			.itch_mwcb_decline_level_v_o(dec_mwcb_decline_level_v[i]),
			.itch_mwcb_decline_level_stock_locate_o(dec_mwcb_decline_level_stock_locate[i]),
			.itch_mwcb_decline_level_tracking_number_o(dec_mwcb_decline_level_tracking_number[i]),
			.itch_mwcb_decline_level_timestamp_o(dec_mwcb_decline_level_timestamp[i]),
			.itch_mwcb_decline_level_level_1_o(dec_mwcb_decline_level_level_1[i]),
			.itch_mwcb_decline_level_level_2_o(dec_mwcb_decline_level_level_2[i]),
			.itch_mwcb_decline_level_level_3_o(dec_mwcb_decline_level_level_3[i]),
			
			.itch_mwcb_status_v_o(dec_mwcb_status_v[i]),
			.itch_mwcb_status_stock_locate_o(dec_mwcb_status_stock_locate[i]),
			.itch_mwcb_status_tracking_number_o(dec_mwcb_status_tracking_number[i]),
			.itch_mwcb_status_timestamp_o(dec_mwcb_status_timestamp[i]),
			.itch_mwcb_status_breached_level_o(dec_mwcb_status_breached_level[i]),
			
			.itch_ipo_quoting_period_update_v_o(dec_ipo_quoting_period_update_v[i]),
			.itch_ipo_quoting_period_update_stock_locate_o(dec_ipo_quoting_period_update_stock_locate[i]),
			.itch_ipo_quoting_period_update_tracking_number_o(dec_ipo_quoting_period_update_tracking_number[i]),
			.itch_ipo_quoting_period_update_timestamp_o(dec_ipo_quoting_period_update_timestamp[i]),
			.itch_ipo_quoting_period_update_stock_o(dec_ipo_quoting_period_update_stock[i]),
			.itch_ipo_quoting_period_update_ipo_quotation_release_time_o(dec_ipo_quoting_period_update_ipo_quotation_release_time[i]),
			.itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o(dec_ipo_quoting_period_update_ipo_quotation_release_qualifier[i]),
			.itch_ipo_quoting_period_update_ipo_price_o(dec_ipo_quoting_period_update_ipo_price[i]),
			
			.itch_luld_auction_collar_v_o(dec_luld_auction_collar_v[i]),
			.itch_luld_auction_collar_stock_locate_o(dec_luld_auction_collar_stock_locate[i]),
			.itch_luld_auction_collar_tracking_number_o(dec_luld_auction_collar_tracking_number[i]),
			.itch_luld_auction_collar_timestamp_o(dec_luld_auction_collar_timestamp[i]),
			.itch_luld_auction_collar_stock_o(dec_luld_auction_collar_stock[i]),
			.itch_luld_auction_collar_auction_collar_reference_price_o(dec_luld_auction_collar_auction_collar_reference_price[i]),
			.itch_luld_auction_collar_upper_auction_collar_price_o(dec_luld_auction_collar_upper_auction_collar_price[i]),
			.itch_luld_auction_collar_lower_auction_collar_price_o(dec_luld_auction_collar_lower_auction_collar_price[i]),
			.itch_luld_auction_collar_auction_collar_extension_o(dec_luld_auction_collar_auction_collar_extension[i]),
			
			.itch_operational_halt_v_o(dec_operational_halt_v[i]),
			.itch_operational_halt_stock_locate_o(dec_operational_halt_stock_locate[i]),
			.itch_operational_halt_tracking_number_o(dec_operational_halt_tracking_number[i]),
			.itch_operational_halt_timestamp_o(dec_operational_halt_timestamp[i]),
			.itch_operational_halt_stock_o(dec_operational_halt_stock[i]),
			.itch_operational_halt_market_code_o(dec_operational_halt_market_code[i]),
			.itch_operational_halt_operational_halt_action_o(dec_operational_halt_operational_halt_action[i]),
			
			.itch_add_order_v_o(dec_add_order_v[i]),
			.itch_add_order_stock_locate_o(dec_add_order_stock_locate[i]),
			.itch_add_order_tracking_number_o(dec_add_order_tracking_number[i]),
			.itch_add_order_timestamp_o(dec_add_order_timestamp[i]),
			.itch_add_order_order_reference_number_o(dec_add_order_order_reference_number[i]),
			.itch_add_order_buy_sell_indicator_o(dec_add_order_buy_sell_indicator[i]),
			.itch_add_order_shares_o(dec_add_order_shares[i]),
			.itch_add_order_stock_o(dec_add_order_stock[i]),
			.itch_add_order_price_o(dec_add_order_price[i]),
			
			.itch_add_order_with_mpid_v_o(dec_add_order_with_mpid_v[i]),
			.itch_add_order_with_mpid_stock_locate_o(dec_add_order_with_mpid_stock_locate[i]),
			.itch_add_order_with_mpid_tracking_number_o(dec_add_order_with_mpid_tracking_number[i]),
			.itch_add_order_with_mpid_timestamp_o(dec_add_order_with_mpid_timestamp[i]),
			.itch_add_order_with_mpid_order_reference_number_o(dec_add_order_with_mpid_order_reference_number[i]),
			.itch_add_order_with_mpid_buy_sell_indicator_o(dec_add_order_with_mpid_buy_sell_indicator[i]),
			.itch_add_order_with_mpid_shares_o(dec_add_order_with_mpid_shares[i]),
			.itch_add_order_with_mpid_stock_o(dec_add_order_with_mpid_stock[i]),
			.itch_add_order_with_mpid_price_o(dec_add_order_with_mpid_price[i]),
			.itch_add_order_with_mpid_attribution_o(dec_add_order_with_mpid_attribution[i]),
			
			.itch_order_executed_v_o(dec_order_executed_v[i]),
			.itch_order_executed_stock_locate_o(dec_order_executed_stock_locate[i]),
			.itch_order_executed_tracking_number_o(dec_order_executed_tracking_number[i]),
			.itch_order_executed_timestamp_o(dec_order_executed_timestamp[i]),
			.itch_order_executed_order_reference_number_o(dec_order_executed_order_reference_number[i]),
			.itch_order_executed_executed_shares_o(dec_order_executed_executed_shares[i]),
			.itch_order_executed_match_number_o(dec_order_executed_match_number[i]),
			
			.itch_order_executed_with_price_v_o(dec_order_executed_with_price_v[i]),
			.itch_order_executed_with_price_stock_locate_o(dec_order_executed_with_price_stock_locate[i]),
			.itch_order_executed_with_price_tracking_number_o(dec_order_executed_with_price_tracking_number[i]),
			.itch_order_executed_with_price_timestamp_o(dec_order_executed_with_price_timestamp[i]),
			.itch_order_executed_with_price_order_reference_number_o(dec_order_executed_with_price_order_reference_number[i]),
			.itch_order_executed_with_price_executed_shares_o(dec_order_executed_with_price_executed_shares[i]),
			.itch_order_executed_with_price_match_number_o(dec_order_executed_with_price_match_number[i]),
			.itch_order_executed_with_price_printable_o(dec_order_executed_with_price_printable[i]),
			.itch_order_executed_with_price_execution_price_o(dec_order_executed_with_price_execution_price[i]),
			
			.itch_order_cancel_v_o(dec_order_cancel_v[i]),
			.itch_order_cancel_stock_locate_o(dec_order_cancel_stock_locate[i]),
			.itch_order_cancel_tracking_number_o(dec_order_cancel_tracking_number[i]),
			.itch_order_cancel_timestamp_o(dec_order_cancel_timestamp[i]),
			.itch_order_cancel_order_reference_number_o(dec_order_cancel_order_reference_number[i]),
			.itch_order_cancel_cancelled_shares_o(dec_order_cancel_cancelled_shares[i]),
			
			.itch_order_delete_v_o(dec_order_delete_v[i]),
			.itch_order_delete_stock_locate_o(dec_order_delete_stock_locate[i]),
			.itch_order_delete_tracking_number_o(dec_order_delete_tracking_number[i]),
			.itch_order_delete_timestamp_o(dec_order_delete_timestamp[i]),
			.itch_order_delete_order_reference_number_o(dec_order_delete_order_reference_number[i]),
			
			.itch_order_replace_v_o(dec_order_replace_v[i]),
			.itch_order_replace_stock_locate_o(dec_order_replace_stock_locate[i]),
			.itch_order_replace_tracking_number_o(dec_order_replace_tracking_number[i]),
			.itch_order_replace_timestamp_o(dec_order_replace_timestamp[i]),
			.itch_order_replace_original_order_reference_number_o(dec_order_replace_original_order_reference_number[i]),
			.itch_order_replace_new_order_reference_number_o(dec_order_replace_new_order_reference_number[i]),
			.itch_order_replace_shares_o(dec_order_replace_shares[i]),
			.itch_order_replace_price_o(dec_order_replace_price[i]),
			
			.itch_trade_v_o(dec_trade_v[i]),
			.itch_trade_stock_locate_o(dec_trade_stock_locate[i]),
			.itch_trade_tracking_number_o(dec_trade_tracking_number[i]),
			.itch_trade_timestamp_o(dec_trade_timestamp[i]),
			.itch_trade_order_reference_number_o(dec_trade_order_reference_number[i]),
			.itch_trade_buy_sell_indicator_o(dec_trade_buy_sell_indicator[i]),
			.itch_trade_shares_o(dec_trade_shares[i]),
			.itch_trade_stock_o(dec_trade_stock[i]),
			.itch_trade_price_o(dec_trade_price[i]),
			.itch_trade_match_number_o(dec_trade_match_number[i]),
			
			.itch_cross_trade_v_o(dec_cross_trade_v[i]),
			.itch_cross_trade_stock_locate_o(dec_cross_trade_stock_locate[i]),
			.itch_cross_trade_tracking_number_o(dec_cross_trade_tracking_number[i]),
			.itch_cross_trade_timestamp_o(dec_cross_trade_timestamp[i]),
			.itch_cross_trade_shares_o(dec_cross_trade_shares[i]),
			.itch_cross_trade_stock_o(dec_cross_trade_stock[i]),
			.itch_cross_trade_cross_price_o(dec_cross_trade_cross_price[i]),
			.itch_cross_trade_match_number_o(dec_cross_trade_match_number[i]),
			.itch_cross_trade_cross_type_o(dec_cross_trade_cross_type[i]),
			
			.itch_broken_trade_v_o(dec_broken_trade_v[i]),
			.itch_broken_trade_stock_locate_o(dec_broken_trade_stock_locate[i]),
			.itch_broken_trade_tracking_number_o(dec_broken_trade_tracking_number[i]),
			.itch_broken_trade_timestamp_o(dec_broken_trade_timestamp[i]),
			.itch_broken_trade_match_number_o(dec_broken_trade_match_number[i]),
			
			.itch_net_order_imbalance_indicator_v_o(dec_net_order_imbalance_indicator_v[i]),
			.itch_net_order_imbalance_indicator_stock_locate_o(dec_net_order_imbalance_indicator_stock_locate[i]),
			.itch_net_order_imbalance_indicator_tracking_number_o(dec_net_order_imbalance_indicator_tracking_number[i]),
			.itch_net_order_imbalance_indicator_timestamp_o(dec_net_order_imbalance_indicator_timestamp[i]),
			.itch_net_order_imbalance_indicator_paired_shares_o(dec_net_order_imbalance_indicator_paired_shares[i]),
			.itch_net_order_imbalance_indicator_imbalance_shares_o(dec_net_order_imbalance_indicator_imbalance_shares[i]),
			.itch_net_order_imbalance_indicator_imbalance_direction_o(dec_net_order_imbalance_indicator_imbalance_direction[i]),
			.itch_net_order_imbalance_indicator_stock_o(dec_net_order_imbalance_indicator_stock[i]),
			.itch_net_order_imbalance_indicator_far_price_o(dec_net_order_imbalance_indicator_far_price[i]),
			.itch_net_order_imbalance_indicator_near_price_o(dec_net_order_imbalance_indicator_near_price[i]),
			.itch_net_order_imbalance_indicator_current_reference_price_o(dec_net_order_imbalance_indicator_current_reference_price[i]),
			.itch_net_order_imbalance_indicator_cross_type_o(dec_net_order_imbalance_indicator_cross_type[i]),
			.itch_net_order_imbalance_indicator_price_variation_indicator_o(dec_net_order_imbalance_indicator_price_variation_indicator[i]),
			
			`ifdef GLIMPSE
			.itch_end_of_snapshot_v_o(dec_end_of_snapshot_v[i]),
			.itch_end_of_snapshot_sequence_number_o(dec_end_of_snapshot_sequence_number[i]),
			`endif
			
			.itch_retail_price_improvement_indicator_v_o(dec_retail_price_improvement_indicator_v[i]),
			.itch_retail_price_improvement_indicator_stock_locate_o(dec_retail_price_improvement_indicator_stock_locate[i]),
			.itch_retail_price_improvement_indicator_tracking_number_o(dec_retail_price_improvement_indicator_tracking_number[i]),
			.itch_retail_price_improvement_indicator_timestamp_o(dec_retail_price_improvement_indicator_timestamp[i]),
			.itch_retail_price_improvement_indicator_stock_o(dec_retail_price_improvement_indicator_stock[i]),
			.itch_retail_price_improvement_indicator_interest_flag_o(dec_retail_price_improvement_indicator_interest_flag[i])
		);
	end
endgenerate
endmodule
