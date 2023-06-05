
output logic msg_system_event_v_o,
output logic [1*LEN-1:0] msg_system_event_message_type_o,
output logic [2*LEN-1:0] msg_system_event_stock_locate_o,
output logic [2*LEN-1:0] msg_system_event_tracking_number_o,
output logic [6*LEN-1:0] msg_system_event_timestamp_o,
output logic [1*LEN-1:0] msg_system_event_event_code_o,

output logic msg_stock_directory_v_o,
output logic [1*LEN-1:0] msg_stock_directory_message_type_o,
output logic [2*LEN-1:0] msg_stock_directory_stock_locate_o,
output logic [2*LEN-1:0] msg_stock_directory_tracking_number_o,
output logic [6*LEN-1:0] msg_stock_directory_timestamp_o,
output logic [8*LEN-1:0] msg_stock_directory_stock_o,
output logic [1*LEN-1:0] msg_stock_directory_market_category_o,
output logic [1*LEN-1:0] msg_stock_directory_financial_status_indicator_o,
output logic [4*LEN-1:0] msg_stock_directory_round_lot_size_o,
output logic [1*LEN-1:0] msg_stock_directory_round_lots_only_o,
output logic [1*LEN-1:0] msg_stock_directory_issue_classification_o,
output logic [2*LEN-1:0] msg_stock_directory_issue_sub_type_o,
output logic [1*LEN-1:0] msg_stock_directory_authenticity_o,
output logic [1*LEN-1:0] msg_stock_directory_short_sale_threshold_indicator_o,
output logic [1*LEN-1:0] msg_stock_directory_ipo_flag_o,
output logic [1*LEN-1:0] msg_stock_directory_luld_reference_price_tier_o,
output logic [1*LEN-1:0] msg_stock_directory_etp_flag_o,
output logic [4*LEN-1:0] msg_stock_directory_etp_leverage_factor_o,
output logic [1*LEN-1:0] msg_stock_directory_inverse_indicator_o,

output logic msg_stock_trading_action_v_o,
output logic [1*LEN-1:0] msg_stock_trading_action_message_type_o,
output logic [2*LEN-1:0] msg_stock_trading_action_stock_locate_o,
output logic [2*LEN-1:0] msg_stock_trading_action_tracking_number_o,
output logic [6*LEN-1:0] msg_stock_trading_action_timestamp_o,
output logic [8*LEN-1:0] msg_stock_trading_action_stock_o,
output logic [1*LEN-1:0] msg_stock_trading_action_trading_state_o,
output logic [1*LEN-1:0] msg_stock_trading_action_reserved_o,
output logic [4*LEN-1:0] msg_stock_trading_action_reason_o,

output logic msg_reg_sho_restriction_v_o,
output logic [1*LEN-1:0] msg_reg_sho_restriction_message_type_o,
output logic [2*LEN-1:0] msg_reg_sho_restriction_stock_locate_o,
output logic [2*LEN-1:0] msg_reg_sho_restriction_tracking_number_o,
output logic [6*LEN-1:0] msg_reg_sho_restriction_timestamp_o,
output logic [8*LEN-1:0] msg_reg_sho_restriction_stock_o,
output logic [1*LEN-1:0] msg_reg_sho_restriction_reg_sho_action_o,

output logic msg_market_participant_position_v_o,
output logic [1*LEN-1:0] msg_market_participant_position_message_type_o,
output logic [2*LEN-1:0] msg_market_participant_position_stock_locate_o,
output logic [2*LEN-1:0] msg_market_participant_position_tracking_number_o,
output logic [6*LEN-1:0] msg_market_participant_position_timestamp_o,
output logic [4*LEN-1:0] msg_market_participant_position_mpid_o,
output logic [8*LEN-1:0] msg_market_participant_position_stock_o,
output logic [1*LEN-1:0] msg_market_participant_position_primary_market_maker_o,
output logic [1*LEN-1:0] msg_market_participant_position_market_maker_mode_o,
output logic [1*LEN-1:0] msg_market_participant_position_market_participant_state_o,

output logic msg_mwcb_decline_level_v_o,
output logic [1*LEN-1:0] msg_mwcb_decline_level_message_type_o,
output logic [2*LEN-1:0] msg_mwcb_decline_level_stock_locate_o,
output logic [2*LEN-1:0] msg_mwcb_decline_level_tracking_number_o,
output logic [6*LEN-1:0] msg_mwcb_decline_level_timestamp_o,
output logic [8*LEN-1:0] msg_mwcb_decline_level_level_1_o,
output logic [8*LEN-1:0] msg_mwcb_decline_level_level_2_o,
output logic [8*LEN-1:0] msg_mwcb_decline_level_level_3_o,

output logic msg_mwcb_status_v_o,
output logic [1*LEN-1:0] msg_mwcb_status_message_type_o,
output logic [2*LEN-1:0] msg_mwcb_status_stock_locate_o,
output logic [2*LEN-1:0] msg_mwcb_status_tracking_number_o,
output logic [6*LEN-1:0] msg_mwcb_status_timestamp_o,
output logic [1*LEN-1:0] msg_mwcb_status_breached_level_o,

output logic msg_ipo_quoting_period_update_v_o,
output logic [1*LEN-1:0] msg_ipo_quoting_period_update_message_type_o,
output logic [2*LEN-1:0] msg_ipo_quoting_period_update_stock_locate_o,
output logic [2*LEN-1:0] msg_ipo_quoting_period_update_tracking_number_o,
output logic [6*LEN-1:0] msg_ipo_quoting_period_update_timestamp_o,
output logic [8*LEN-1:0] msg_ipo_quoting_period_update_stock_o,
output logic [4*LEN-1:0] msg_ipo_quoting_period_update_ipo_quotation_release_time_o,
output logic [1*LEN-1:0] msg_ipo_quoting_period_update_ipo_quotation_release_qualifier_o,
output logic [4*LEN-1:0] msg_ipo_quoting_period_update_ipo_price_o,

output logic msg_luld_auction_collar_v_o,
output logic [1*LEN-1:0] msg_luld_auction_collar_message_type_o,
output logic [2*LEN-1:0] msg_luld_auction_collar_stock_locate_o,
output logic [2*LEN-1:0] msg_luld_auction_collar_tracking_number_o,
output logic [6*LEN-1:0] msg_luld_auction_collar_timestamp_o,
output logic [8*LEN-1:0] msg_luld_auction_collar_stock_o,
output logic [4*LEN-1:0] msg_luld_auction_collar_auction_collar_reference_price_o,
output logic [4*LEN-1:0] msg_luld_auction_collar_upper_auction_collar_price_o,
output logic [4*LEN-1:0] msg_luld_auction_collar_lower_auction_collar_price_o,
output logic [4*LEN-1:0] msg_luld_auction_collar_auction_collar_extension_o,

output logic msg_operational_halt_v_o,
output logic [1*LEN-1:0] msg_operational_halt_message_type_o,
output logic [2*LEN-1:0] msg_operational_halt_stock_locate_o,
output logic [2*LEN-1:0] msg_operational_halt_tracking_number_o,
output logic [6*LEN-1:0] msg_operational_halt_timestamp_o,
output logic [8*LEN-1:0] msg_operational_halt_stock_o,
output logic [1*LEN-1:0] msg_operational_halt_market_code_o,
output logic [1*LEN-1:0] msg_operational_halt_operational_halt_action_o,

output logic msg_add_order_v_o,
output logic [1*LEN-1:0] msg_add_order_message_type_o,
output logic [2*LEN-1:0] msg_add_order_stock_locate_o,
output logic [2*LEN-1:0] msg_add_order_tracking_number_o,
output logic [6*LEN-1:0] msg_add_order_timestamp_o,
output logic [8*LEN-1:0] msg_add_order_order_reference_number_o,
output logic [1*LEN-1:0] msg_add_order_buy_sell_indicator_o,
output logic [4*LEN-1:0] msg_add_order_shares_o,
output logic [8*LEN-1:0] msg_add_order_stock_o,
output logic [4*LEN-1:0] msg_add_order_price_o,

output logic msg_add_order_with_mpid_v_o,
output logic [1*LEN-1:0] msg_add_order_with_mpid_message_type_o,
output logic [2*LEN-1:0] msg_add_order_with_mpid_stock_locate_o,
output logic [2*LEN-1:0] msg_add_order_with_mpid_tracking_number_o,
output logic [6*LEN-1:0] msg_add_order_with_mpid_timestamp_o,
output logic [8*LEN-1:0] msg_add_order_with_mpid_order_reference_number_o,
output logic [1*LEN-1:0] msg_add_order_with_mpid_buy_sell_indicator_o,
output logic [4*LEN-1:0] msg_add_order_with_mpid_shares_o,
output logic [8*LEN-1:0] msg_add_order_with_mpid_stock_o,
output logic [4*LEN-1:0] msg_add_order_with_mpid_price_o,
output logic [4*LEN-1:0] msg_add_order_with_mpid_attribution_o,

output logic msg_order_executed_v_o,
output logic [1*LEN-1:0] msg_order_executed_message_type_o,
output logic [2*LEN-1:0] msg_order_executed_stock_locate_o,
output logic [2*LEN-1:0] msg_order_executed_tracking_number_o,
output logic [6*LEN-1:0] msg_order_executed_timestamp_o,
output logic [8*LEN-1:0] msg_order_executed_order_reference_number_o,
output logic [4*LEN-1:0] msg_order_executed_executed_shares_o,
output logic [8*LEN-1:0] msg_order_executed_match_number_o,

output logic msg_order_executed_with_price_v_o,
output logic [1*LEN-1:0] msg_order_executed_with_price_message_type_o,
output logic [2*LEN-1:0] msg_order_executed_with_price_stock_locate_o,
output logic [2*LEN-1:0] msg_order_executed_with_price_tracking_number_o,
output logic [6*LEN-1:0] msg_order_executed_with_price_timestamp_o,
output logic [8*LEN-1:0] msg_order_executed_with_price_order_reference_number_o,
output logic [4*LEN-1:0] msg_order_executed_with_price_executed_shares_o,
output logic [8*LEN-1:0] msg_order_executed_with_price_match_number_o,
output logic [1*LEN-1:0] msg_order_executed_with_price_printable_o,
output logic [4*LEN-1:0] msg_order_executed_with_price_execution_price_o,

output logic msg_order_cancel_v_o,
output logic [1*LEN-1:0] msg_order_cancel_message_type_o,
output logic [2*LEN-1:0] msg_order_cancel_stock_locate_o,
output logic [2*LEN-1:0] msg_order_cancel_tracking_number_o,
output logic [6*LEN-1:0] msg_order_cancel_timestamp_o,
output logic [8*LEN-1:0] msg_order_cancel_order_reference_number_o,
output logic [4*LEN-1:0] msg_order_cancel_cancelled_shares_o,

output logic msg_order_delete_v_o,
output logic [1*LEN-1:0] msg_order_delete_message_type_o,
output logic [2*LEN-1:0] msg_order_delete_stock_locate_o,
output logic [2*LEN-1:0] msg_order_delete_tracking_number_o,
output logic [6*LEN-1:0] msg_order_delete_timestamp_o,
output logic [8*LEN-1:0] msg_order_delete_order_reference_number_o,

output logic msg_order_replace_v_o,
output logic [1*LEN-1:0] msg_order_replace_message_type_o,
output logic [2*LEN-1:0] msg_order_replace_stock_locate_o,
output logic [2*LEN-1:0] msg_order_replace_tracking_number_o,
output logic [6*LEN-1:0] msg_order_replace_timestamp_o,
output logic [8*LEN-1:0] msg_order_replace_original_order_reference_number_o,
output logic [8*LEN-1:0] msg_order_replace_new_order_reference_number_o,
output logic [4*LEN-1:0] msg_order_replace_shares_o,
output logic [4*LEN-1:0] msg_order_replace_price_o,

output logic msg_trade_v_o,
output logic [1*LEN-1:0] msg_trade_message_type_o,
output logic [2*LEN-1:0] msg_trade_stock_locate_o,
output logic [2*LEN-1:0] msg_trade_tracking_number_o,
output logic [6*LEN-1:0] msg_trade_timestamp_o,
output logic [8*LEN-1:0] msg_trade_order_reference_number_o,
output logic [1*LEN-1:0] msg_trade_buy_sell_indicator_o,
output logic [4*LEN-1:0] msg_trade_shares_o,
output logic [8*LEN-1:0] msg_trade_stock_o,
output logic [4*LEN-1:0] msg_trade_price_o,
output logic [8*LEN-1:0] msg_trade_match_number_o,

output logic msg_cross_trade_v_o,
output logic [1*LEN-1:0] msg_cross_trade_message_type_o,
output logic [2*LEN-1:0] msg_cross_trade_stock_locate_o,
output logic [2*LEN-1:0] msg_cross_trade_tracking_number_o,
output logic [6*LEN-1:0] msg_cross_trade_timestamp_o,
output logic [8*LEN-1:0] msg_cross_trade_shares_o,
output logic [8*LEN-1:0] msg_cross_trade_stock_o,
output logic [4*LEN-1:0] msg_cross_trade_cross_price_o,
output logic [8*LEN-1:0] msg_cross_trade_match_number_o,
output logic [1*LEN-1:0] msg_cross_trade_cross_type_o,

output logic msg_broken_trade_v_o,
output logic [1*LEN-1:0] msg_broken_trade_message_type_o,
output logic [2*LEN-1:0] msg_broken_trade_stock_locate_o,
output logic [2*LEN-1:0] msg_broken_trade_tracking_number_o,
output logic [6*LEN-1:0] msg_broken_trade_timestamp_o,
output logic [8*LEN-1:0] msg_broken_trade_match_number_o,

output logic msg_net_order_imbalance_indicator_v_o,
output logic [1*LEN-1:0] msg_net_order_imbalance_indicator_message_type_o,
output logic [2*LEN-1:0] msg_net_order_imbalance_indicator_stock_locate_o,
output logic [2*LEN-1:0] msg_net_order_imbalance_indicator_tracking_number_o,
output logic [6*LEN-1:0] msg_net_order_imbalance_indicator_timestamp_o,
output logic [8*LEN-1:0] msg_net_order_imbalance_indicator_paired_shares_o,
output logic [8*LEN-1:0] msg_net_order_imbalance_indicator_imbalance_shares_o,
output logic [1*LEN-1:0] msg_net_order_imbalance_indicator_imbalance_direction_o,
output logic [8*LEN-1:0] msg_net_order_imbalance_indicator_stock_o,
output logic [4*LEN-1:0] msg_net_order_imbalance_indicator_far_price_o,
output logic [4*LEN-1:0] msg_net_order_imbalance_indicator_near_price_o,
output logic [4*LEN-1:0] msg_net_order_imbalance_indicator_current_reference_price_o,
output logic [1*LEN-1:0] msg_net_order_imbalance_indicator_cross_type_o,
output logic [1*LEN-1:0] msg_net_order_imbalance_indicator_price_variation_indicator_o,

output logic msg_retail_price_improvement_indicator_v_o,
output logic [1*LEN-1:0] msg_retail_price_improvement_indicator_message_type_o,
output logic [2*LEN-1:0] msg_retail_price_improvement_indicator_stock_locate_o,
output logic [2*LEN-1:0] msg_retail_price_improvement_indicator_tracking_number_o,
output logic [6*LEN-1:0] msg_retail_price_improvement_indicator_timestamp_o,
output logic [8*LEN-1:0] msg_retail_price_improvement_indicator_stock_o,
output logic [1*LEN-1:0] msg_retail_price_improvement_indicator_interest_flag_o,

output logic msg_end_of_snapshot_v_o,
output logic [1*LEN-1:0] msg_end_of_snapshot_message_type_o,
output logic [20*LEN-1:0] msg_end_of_snapshot_sequence_number_o,