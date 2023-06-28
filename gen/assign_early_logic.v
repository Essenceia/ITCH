
assign early_o.system_event_early_v = system_event_lite_v & (data_cnt_q == 'd1);
assign early_o.system_event_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.system_event_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.system_event_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.system_event_event_code_early_lite_v = data_cnt_q >= 'd12;

assign early_o.stock_directory_early_v = stock_directory_lite_v & (data_cnt_q == 'd1);
assign early_o.stock_directory_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.stock_directory_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.stock_directory_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.stock_directory_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.stock_directory_market_category_early_lite_v = data_cnt_q >= 'd20;
assign early_o.stock_directory_financial_status_indicator_early_lite_v = data_cnt_q >= 'd21;
assign early_o.stock_directory_round_lot_size_early_lite_v = data_cnt_q >= 'd25;
assign early_o.stock_directory_round_lots_only_early_lite_v = data_cnt_q >= 'd26;
assign early_o.stock_directory_issue_classification_early_lite_v = data_cnt_q >= 'd27;
assign early_o.stock_directory_issue_sub_type_early_lite_v = data_cnt_q >= 'd29;
assign early_o.stock_directory_authenticity_early_lite_v = data_cnt_q >= 'd30;
assign early_o.stock_directory_short_sale_threshold_indicator_early_lite_v = data_cnt_q >= 'd31;
assign early_o.stock_directory_ipo_flag_early_lite_v = data_cnt_q >= 'd32;
assign early_o.stock_directory_luld_reference_price_tier_early_lite_v = data_cnt_q >= 'd33;
assign early_o.stock_directory_etp_flag_early_lite_v = data_cnt_q >= 'd34;
assign early_o.stock_directory_etp_leverage_factor_early_lite_v = data_cnt_q >= 'd38;
assign early_o.stock_directory_inverse_indicator_early_lite_v = data_cnt_q >= 'd39;

assign early_o.stock_trading_action_early_v = stock_trading_action_lite_v & (data_cnt_q == 'd1);
assign early_o.stock_trading_action_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.stock_trading_action_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.stock_trading_action_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.stock_trading_action_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.stock_trading_action_trading_state_early_lite_v = data_cnt_q >= 'd20;
assign early_o.stock_trading_action_reserved_early_lite_v = data_cnt_q >= 'd21;
assign early_o.stock_trading_action_reason_early_lite_v = data_cnt_q >= 'd25;

assign early_o.reg_sho_restriction_early_v = reg_sho_restriction_lite_v & (data_cnt_q == 'd1);
assign early_o.reg_sho_restriction_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.reg_sho_restriction_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.reg_sho_restriction_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.reg_sho_restriction_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.reg_sho_restriction_reg_sho_action_early_lite_v = data_cnt_q >= 'd20;

assign early_o.market_participant_position_early_v = market_participant_position_lite_v & (data_cnt_q == 'd1);
assign early_o.market_participant_position_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.market_participant_position_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.market_participant_position_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.market_participant_position_mpid_early_lite_v = data_cnt_q >= 'd15;
assign early_o.market_participant_position_stock_early_lite_v = data_cnt_q >= 'd23;
assign early_o.market_participant_position_primary_market_maker_early_lite_v = data_cnt_q >= 'd24;
assign early_o.market_participant_position_market_maker_mode_early_lite_v = data_cnt_q >= 'd25;
assign early_o.market_participant_position_market_participant_state_early_lite_v = data_cnt_q >= 'd26;

assign early_o.mwcb_decline_level_early_v = mwcb_decline_level_lite_v & (data_cnt_q == 'd1);
assign early_o.mwcb_decline_level_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.mwcb_decline_level_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.mwcb_decline_level_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.mwcb_decline_level_level_1_early_lite_v = data_cnt_q >= 'd19;
assign early_o.mwcb_decline_level_level_2_early_lite_v = data_cnt_q >= 'd27;
assign early_o.mwcb_decline_level_level_3_early_lite_v = data_cnt_q >= 'd35;

assign early_o.mwcb_status_early_v = mwcb_status_lite_v & (data_cnt_q == 'd1);
assign early_o.mwcb_status_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.mwcb_status_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.mwcb_status_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.mwcb_status_breached_level_early_lite_v = data_cnt_q >= 'd12;

assign early_o.ipo_quoting_period_update_early_v = ipo_quoting_period_update_lite_v & (data_cnt_q == 'd1);
assign early_o.ipo_quoting_period_update_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.ipo_quoting_period_update_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.ipo_quoting_period_update_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.ipo_quoting_period_update_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.ipo_quoting_period_update_ipo_quotation_release_time_early_lite_v = data_cnt_q >= 'd23;
assign early_o.ipo_quoting_period_update_ipo_quotation_release_qualifier_early_lite_v = data_cnt_q >= 'd24;
assign early_o.ipo_quoting_period_update_ipo_price_early_lite_v = data_cnt_q >= 'd28;

assign early_o.luld_auction_collar_early_v = luld_auction_collar_lite_v & (data_cnt_q == 'd1);
assign early_o.luld_auction_collar_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.luld_auction_collar_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.luld_auction_collar_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.luld_auction_collar_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.luld_auction_collar_auction_collar_reference_price_early_lite_v = data_cnt_q >= 'd23;
assign early_o.luld_auction_collar_upper_auction_collar_price_early_lite_v = data_cnt_q >= 'd27;
assign early_o.luld_auction_collar_lower_auction_collar_price_early_lite_v = data_cnt_q >= 'd31;
assign early_o.luld_auction_collar_auction_collar_extension_early_lite_v = data_cnt_q >= 'd35;

assign early_o.operational_halt_early_v = operational_halt_lite_v & (data_cnt_q == 'd1);
assign early_o.operational_halt_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.operational_halt_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.operational_halt_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.operational_halt_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.operational_halt_market_code_early_lite_v = data_cnt_q >= 'd20;
assign early_o.operational_halt_operational_halt_action_early_lite_v = data_cnt_q >= 'd21;

assign early_o.add_order_early_v = add_order_lite_v & (data_cnt_q == 'd1);
assign early_o.add_order_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.add_order_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.add_order_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.add_order_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.add_order_buy_sell_indicator_early_lite_v = data_cnt_q >= 'd20;
assign early_o.add_order_shares_early_lite_v = data_cnt_q >= 'd24;
assign early_o.add_order_stock_early_lite_v = data_cnt_q >= 'd32;
assign early_o.add_order_price_early_lite_v = data_cnt_q >= 'd36;

assign early_o.add_order_with_mpid_early_v = add_order_with_mpid_lite_v & (data_cnt_q == 'd1);
assign early_o.add_order_with_mpid_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.add_order_with_mpid_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.add_order_with_mpid_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.add_order_with_mpid_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.add_order_with_mpid_buy_sell_indicator_early_lite_v = data_cnt_q >= 'd20;
assign early_o.add_order_with_mpid_shares_early_lite_v = data_cnt_q >= 'd24;
assign early_o.add_order_with_mpid_stock_early_lite_v = data_cnt_q >= 'd32;
assign early_o.add_order_with_mpid_price_early_lite_v = data_cnt_q >= 'd36;
assign early_o.add_order_with_mpid_attribution_early_lite_v = data_cnt_q >= 'd40;

assign early_o.order_executed_early_v = order_executed_lite_v & (data_cnt_q == 'd1);
assign early_o.order_executed_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_executed_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_executed_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_executed_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_executed_executed_shares_early_lite_v = data_cnt_q >= 'd23;
assign early_o.order_executed_match_number_early_lite_v = data_cnt_q >= 'd31;

assign early_o.order_executed_with_price_early_v = order_executed_with_price_lite_v & (data_cnt_q == 'd1);
assign early_o.order_executed_with_price_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_executed_with_price_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_executed_with_price_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_executed_with_price_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_executed_with_price_executed_shares_early_lite_v = data_cnt_q >= 'd23;
assign early_o.order_executed_with_price_match_number_early_lite_v = data_cnt_q >= 'd31;
assign early_o.order_executed_with_price_printable_early_lite_v = data_cnt_q >= 'd32;
assign early_o.order_executed_with_price_execution_price_early_lite_v = data_cnt_q >= 'd36;

assign early_o.order_cancel_early_v = order_cancel_lite_v & (data_cnt_q == 'd1);
assign early_o.order_cancel_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_cancel_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_cancel_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_cancel_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_cancel_cancelled_shares_early_lite_v = data_cnt_q >= 'd23;

assign early_o.order_delete_early_v = order_delete_lite_v & (data_cnt_q == 'd1);
assign early_o.order_delete_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_delete_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_delete_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_delete_order_reference_number_early_lite_v = data_cnt_q >= 'd19;

assign early_o.order_replace_early_v = order_replace_lite_v & (data_cnt_q == 'd1);
assign early_o.order_replace_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.order_replace_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.order_replace_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.order_replace_original_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.order_replace_new_order_reference_number_early_lite_v = data_cnt_q >= 'd27;
assign early_o.order_replace_shares_early_lite_v = data_cnt_q >= 'd31;
assign early_o.order_replace_price_early_lite_v = data_cnt_q >= 'd35;

assign early_o.trade_early_v = trade_lite_v & (data_cnt_q == 'd1);
assign early_o.trade_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.trade_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.trade_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.trade_order_reference_number_early_lite_v = data_cnt_q >= 'd19;
assign early_o.trade_buy_sell_indicator_early_lite_v = data_cnt_q >= 'd20;
assign early_o.trade_shares_early_lite_v = data_cnt_q >= 'd24;
assign early_o.trade_stock_early_lite_v = data_cnt_q >= 'd32;
assign early_o.trade_price_early_lite_v = data_cnt_q >= 'd36;
assign early_o.trade_match_number_early_lite_v = data_cnt_q >= 'd44;

assign early_o.cross_trade_early_v = cross_trade_lite_v & (data_cnt_q == 'd1);
assign early_o.cross_trade_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.cross_trade_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.cross_trade_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.cross_trade_shares_early_lite_v = data_cnt_q >= 'd19;
assign early_o.cross_trade_stock_early_lite_v = data_cnt_q >= 'd27;
assign early_o.cross_trade_cross_price_early_lite_v = data_cnt_q >= 'd31;
assign early_o.cross_trade_match_number_early_lite_v = data_cnt_q >= 'd39;
assign early_o.cross_trade_cross_type_early_lite_v = data_cnt_q >= 'd40;

assign early_o.broken_trade_early_v = broken_trade_lite_v & (data_cnt_q == 'd1);
assign early_o.broken_trade_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.broken_trade_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.broken_trade_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.broken_trade_match_number_early_lite_v = data_cnt_q >= 'd19;

assign early_o.net_order_imbalance_indicator_early_v = net_order_imbalance_indicator_lite_v & (data_cnt_q == 'd1);
assign early_o.net_order_imbalance_indicator_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.net_order_imbalance_indicator_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.net_order_imbalance_indicator_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.net_order_imbalance_indicator_paired_shares_early_lite_v = data_cnt_q >= 'd19;
assign early_o.net_order_imbalance_indicator_imbalance_shares_early_lite_v = data_cnt_q >= 'd27;
assign early_o.net_order_imbalance_indicator_imbalance_direction_early_lite_v = data_cnt_q >= 'd28;
assign early_o.net_order_imbalance_indicator_stock_early_lite_v = data_cnt_q >= 'd36;
assign early_o.net_order_imbalance_indicator_far_price_early_lite_v = data_cnt_q >= 'd40;
assign early_o.net_order_imbalance_indicator_near_price_early_lite_v = data_cnt_q >= 'd44;
assign early_o.net_order_imbalance_indicator_current_reference_price_early_lite_v = data_cnt_q >= 'd48;
assign early_o.net_order_imbalance_indicator_cross_type_early_lite_v = data_cnt_q >= 'd49;
assign early_o.net_order_imbalance_indicator_price_variation_indicator_early_lite_v = data_cnt_q >= 'd50;

assign early_o.retail_price_improvement_indicator_early_v = retail_price_improvement_indicator_lite_v & (data_cnt_q == 'd1);
assign early_o.retail_price_improvement_indicator_stock_locate_early_lite_v = data_cnt_q >= 'd3;
assign early_o.retail_price_improvement_indicator_tracking_number_early_lite_v = data_cnt_q >= 'd5;
assign early_o.retail_price_improvement_indicator_timestamp_early_lite_v = data_cnt_q >= 'd11;
assign early_o.retail_price_improvement_indicator_stock_early_lite_v = data_cnt_q >= 'd19;
assign early_o.retail_price_improvement_indicator_interest_flag_early_lite_v = data_cnt_q >= 'd20;

assign early_o.end_of_snapshot_early_v = end_of_snapshot_lite_v & (data_cnt_q == 'd1);
assign early_o.end_of_snapshot_sequence_number_early_lite_v = data_cnt_q >= 'd21;
