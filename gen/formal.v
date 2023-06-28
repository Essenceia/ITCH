sva_xcheck_system_event_v : assert( ~$isunknown(system_event_v));
sva_xcheck_system_evendata : assert( ~system_event_v | (system_event_v & ~$isunknown((|system_event_stock_locate | |system_event_tracking_number | |system_event_timestamp | |system_event_event_code))));

sva_xcheck_stock_directory_v : assert( ~$isunknown(stock_directory_v));
sva_xcheck_stock_directordata : assert( ~stock_directory_v | (stock_directory_v & ~$isunknown((|stock_directory_stock_locate | |stock_directory_tracking_number | |stock_directory_timestamp | |stock_directory_stock | |stock_directory_market_category | |stock_directory_financial_status_indicator | |stock_directory_round_lot_size | |stock_directory_round_lots_only | |stock_directory_issue_classification | |stock_directory_issue_sub_type | |stock_directory_authenticity | |stock_directory_short_sale_threshold_indicator | |stock_directory_ipo_flag | |stock_directory_luld_reference_price_tier | |stock_directory_etp_flag | |stock_directory_etp_leverage_factor | |stock_directory_inverse_indicator))));

sva_xcheck_stock_trading_action_v : assert( ~$isunknown(stock_trading_action_v));
sva_xcheck_stock_trading_actiodata : assert( ~stock_trading_action_v | (stock_trading_action_v & ~$isunknown((|stock_trading_action_stock_locate | |stock_trading_action_tracking_number | |stock_trading_action_timestamp | |stock_trading_action_stock | |stock_trading_action_trading_state | |stock_trading_action_reserved | |stock_trading_action_reason))));

sva_xcheck_reg_sho_restriction_v : assert( ~$isunknown(reg_sho_restriction_v));
sva_xcheck_reg_sho_restrictiodata : assert( ~reg_sho_restriction_v | (reg_sho_restriction_v & ~$isunknown((|reg_sho_restriction_stock_locate | |reg_sho_restriction_tracking_number | |reg_sho_restriction_timestamp | |reg_sho_restriction_stock | |reg_sho_restriction_reg_sho_action))));

sva_xcheck_market_participant_position_v : assert( ~$isunknown(market_participant_position_v));
sva_xcheck_market_participant_positiodata : assert( ~market_participant_position_v | (market_participant_position_v & ~$isunknown((|market_participant_position_stock_locate | |market_participant_position_tracking_number | |market_participant_position_timestamp | |market_participant_position_mpid | |market_participant_position_stock | |market_participant_position_primary_market_maker | |market_participant_position_market_maker_mode | |market_participant_position_market_participant_state))));

sva_xcheck_mwcb_decline_level_v : assert( ~$isunknown(mwcb_decline_level_v));
sva_xcheck_mwcb_decline_levedata : assert( ~mwcb_decline_level_v | (mwcb_decline_level_v & ~$isunknown((|mwcb_decline_level_stock_locate | |mwcb_decline_level_tracking_number | |mwcb_decline_level_timestamp | |mwcb_decline_level_level_1 | |mwcb_decline_level_level_2 | |mwcb_decline_level_level_3))));

sva_xcheck_mwcb_status_v : assert( ~$isunknown(mwcb_status_v));
sva_xcheck_mwcb_statudata : assert( ~mwcb_status_v | (mwcb_status_v & ~$isunknown((|mwcb_status_stock_locate | |mwcb_status_tracking_number | |mwcb_status_timestamp | |mwcb_status_breached_level))));

sva_xcheck_ipo_quoting_period_update_v : assert( ~$isunknown(ipo_quoting_period_update_v));
sva_xcheck_ipo_quoting_period_updatdata : assert( ~ipo_quoting_period_update_v | (ipo_quoting_period_update_v & ~$isunknown((|ipo_quoting_period_update_stock_locate | |ipo_quoting_period_update_tracking_number | |ipo_quoting_period_update_timestamp | |ipo_quoting_period_update_stock | |ipo_quoting_period_update_ipo_quotation_release_time | |ipo_quoting_period_update_ipo_quotation_release_qualifier | |ipo_quoting_period_update_ipo_price))));

sva_xcheck_luld_auction_collar_v : assert( ~$isunknown(luld_auction_collar_v));
sva_xcheck_luld_auction_colladata : assert( ~luld_auction_collar_v | (luld_auction_collar_v & ~$isunknown((|luld_auction_collar_stock_locate | |luld_auction_collar_tracking_number | |luld_auction_collar_timestamp | |luld_auction_collar_stock | |luld_auction_collar_auction_collar_reference_price | |luld_auction_collar_upper_auction_collar_price | |luld_auction_collar_lower_auction_collar_price | |luld_auction_collar_auction_collar_extension))));

sva_xcheck_operational_halt_v : assert( ~$isunknown(operational_halt_v));
sva_xcheck_operational_haldata : assert( ~operational_halt_v | (operational_halt_v & ~$isunknown((|operational_halt_stock_locate | |operational_halt_tracking_number | |operational_halt_timestamp | |operational_halt_stock | |operational_halt_market_code | |operational_halt_operational_halt_action))));

sva_xcheck_add_order_v : assert( ~$isunknown(add_order_v));
sva_xcheck_add_ordedata : assert( ~add_order_v | (add_order_v & ~$isunknown((|add_order_stock_locate | |add_order_tracking_number | |add_order_timestamp | |add_order_order_reference_number | |add_order_buy_sell_indicator | |add_order_shares | |add_order_stock | |add_order_price))));

sva_xcheck_add_order_with_mpid_v : assert( ~$isunknown(add_order_with_mpid_v));
sva_xcheck_add_order_with_mpidata : assert( ~add_order_with_mpid_v | (add_order_with_mpid_v & ~$isunknown((|add_order_with_mpid_stock_locate | |add_order_with_mpid_tracking_number | |add_order_with_mpid_timestamp | |add_order_with_mpid_order_reference_number | |add_order_with_mpid_buy_sell_indicator | |add_order_with_mpid_shares | |add_order_with_mpid_stock | |add_order_with_mpid_price | |add_order_with_mpid_attribution))));

sva_xcheck_order_executed_v : assert( ~$isunknown(order_executed_v));
sva_xcheck_order_executedata : assert( ~order_executed_v | (order_executed_v & ~$isunknown((|order_executed_stock_locate | |order_executed_tracking_number | |order_executed_timestamp | |order_executed_order_reference_number | |order_executed_executed_shares | |order_executed_match_number))));

sva_xcheck_order_executed_with_price_v : assert( ~$isunknown(order_executed_with_price_v));
sva_xcheck_order_executed_with_pricdata : assert( ~order_executed_with_price_v | (order_executed_with_price_v & ~$isunknown((|order_executed_with_price_stock_locate | |order_executed_with_price_tracking_number | |order_executed_with_price_timestamp | |order_executed_with_price_order_reference_number | |order_executed_with_price_executed_shares | |order_executed_with_price_match_number | |order_executed_with_price_printable | |order_executed_with_price_execution_price))));

sva_xcheck_order_cancel_v : assert( ~$isunknown(order_cancel_v));
sva_xcheck_order_cancedata : assert( ~order_cancel_v | (order_cancel_v & ~$isunknown((|order_cancel_stock_locate | |order_cancel_tracking_number | |order_cancel_timestamp | |order_cancel_order_reference_number | |order_cancel_cancelled_shares))));

sva_xcheck_order_delete_v : assert( ~$isunknown(order_delete_v));
sva_xcheck_order_deletdata : assert( ~order_delete_v | (order_delete_v & ~$isunknown((|order_delete_stock_locate | |order_delete_tracking_number | |order_delete_timestamp | |order_delete_order_reference_number))));

sva_xcheck_order_replace_v : assert( ~$isunknown(order_replace_v));
sva_xcheck_order_replacdata : assert( ~order_replace_v | (order_replace_v & ~$isunknown((|order_replace_stock_locate | |order_replace_tracking_number | |order_replace_timestamp | |order_replace_original_order_reference_number | |order_replace_new_order_reference_number | |order_replace_shares | |order_replace_price))));

sva_xcheck_trade_v : assert( ~$isunknown(trade_v));
sva_xcheck_traddata : assert( ~trade_v | (trade_v & ~$isunknown((|trade_stock_locate | |trade_tracking_number | |trade_timestamp | |trade_order_reference_number | |trade_buy_sell_indicator | |trade_shares | |trade_stock | |trade_price | |trade_match_number))));

sva_xcheck_cross_trade_v : assert( ~$isunknown(cross_trade_v));
sva_xcheck_cross_traddata : assert( ~cross_trade_v | (cross_trade_v & ~$isunknown((|cross_trade_stock_locate | |cross_trade_tracking_number | |cross_trade_timestamp | |cross_trade_shares | |cross_trade_stock | |cross_trade_cross_price | |cross_trade_match_number | |cross_trade_cross_type))));

sva_xcheck_broken_trade_v : assert( ~$isunknown(broken_trade_v));
sva_xcheck_broken_traddata : assert( ~broken_trade_v | (broken_trade_v & ~$isunknown((|broken_trade_stock_locate | |broken_trade_tracking_number | |broken_trade_timestamp | |broken_trade_match_number))));

sva_xcheck_net_order_imbalance_indicator_v : assert( ~$isunknown(net_order_imbalance_indicator_v));
sva_xcheck_net_order_imbalance_indicatodata : assert( ~net_order_imbalance_indicator_v | (net_order_imbalance_indicator_v & ~$isunknown((|net_order_imbalance_indicator_stock_locate | |net_order_imbalance_indicator_tracking_number | |net_order_imbalance_indicator_timestamp | |net_order_imbalance_indicator_paired_shares | |net_order_imbalance_indicator_imbalance_shares | |net_order_imbalance_indicator_imbalance_direction | |net_order_imbalance_indicator_stock | |net_order_imbalance_indicator_far_price | |net_order_imbalance_indicator_near_price | |net_order_imbalance_indicator_current_reference_price | |net_order_imbalance_indicator_cross_type | |net_order_imbalance_indicator_price_variation_indicator))));

sva_xcheck_retail_price_improvement_indicator_v : assert( ~$isunknown(retail_price_improvement_indicator_v));
sva_xcheck_retail_price_improvement_indicatodata : assert( ~retail_price_improvement_indicator_v | (retail_price_improvement_indicator_v & ~$isunknown((|retail_price_improvement_indicator_stock_locate | |retail_price_improvement_indicator_tracking_number | |retail_price_improvement_indicator_timestamp | |retail_price_improvement_indicator_stock | |retail_price_improvement_indicator_interest_flag))));

sva_xcheck_end_of_snapshot_v : assert( ~$isunknown(end_of_snapshot_v));
sva_xcheck_end_of_snapshodata : assert( ~end_of_snapshot_v | (end_of_snapshot_v & ~$isunknown((|end_of_snapshot_sequence_number))));

sva_itch_msg_valid_onehot0 : assert( $onehot0({system_event_v,stock_directory_v,stock_trading_action_v,reg_sho_restriction_v,market_participant_position_v,mwcb_decline_level_v,mwcb_status_v,ipo_quoting_period_update_v,luld_auction_collar_v,operational_halt_v,add_order_v,add_order_with_mpid_v,order_executed_v,order_executed_with_price_v,order_cancel_v,order_delete_v,order_replace_v,trade_v,cross_trade_v,broken_trade_v,net_order_imbalance_indicator_v,retail_price_improvement_indicator_v,end_of_snapshot_v}));
