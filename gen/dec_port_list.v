
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

.itch_retail_price_improvement_indicator_v_o(dec_retail_price_improvement_indicator_v[i]),
.itch_retail_price_improvement_indicator_stock_locate_o(dec_retail_price_improvement_indicator_stock_locate[i*2*LEN+2*LEN-1:i*2*LEN]),
.itch_retail_price_improvement_indicator_tracking_number_o(dec_retail_price_improvement_indicator_tracking_number[i*2*LEN+2*LEN-1:i*2*LEN]),
.itch_retail_price_improvement_indicator_timestamp_o(dec_retail_price_improvement_indicator_timestamp[i*6*LEN+6*LEN-1:i*6*LEN]),
.itch_retail_price_improvement_indicator_stock_o(dec_retail_price_improvement_indicator_stock[i*8*LEN+8*LEN-1:i*8*LEN]),
.itch_retail_price_improvement_indicator_interest_flag_o(dec_retail_price_improvement_indicator_interest_flag[i*1*LEN+1*LEN-1:i*1*LEN]),

.itch_end_of_snapshot_v_o(dec_end_of_snapshot_v[i]),
.itch_end_of_snapshot_sequence_number_o(dec_end_of_snapshot_sequence_number[i*20*LEN+20*LEN-1:i*20*LEN]),