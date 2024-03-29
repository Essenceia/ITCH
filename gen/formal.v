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
