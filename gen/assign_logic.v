
assign itch_system_event_v_o = (itch_msg_type == 'd83) & (data_cnt_q == 'd2);
assign itch_system_event_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_system_event_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_system_event_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_system_event_event_code_o = data_q[LEN*11+LEN*1-1:LEN*11];

assign itch_stock_directory_v_o = (itch_msg_type == 'd82) & (data_cnt_q == 'd5);
assign itch_stock_directory_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_stock_directory_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_stock_directory_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_stock_directory_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_stock_directory_market_category_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_stock_directory_financial_status_indicator_o = data_q[LEN*20+LEN*1-1:LEN*20];
assign itch_stock_directory_round_lot_size_o = data_q[LEN*21+LEN*4-1:LEN*21];
assign itch_stock_directory_round_lots_only_o = data_q[LEN*25+LEN*1-1:LEN*25];
assign itch_stock_directory_issue_classification_o = data_q[LEN*26+LEN*1-1:LEN*26];
assign itch_stock_directory_issue_sub_type_o = data_q[LEN*27+LEN*2-1:LEN*27];
assign itch_stock_directory_authenticity_o = data_q[LEN*29+LEN*1-1:LEN*29];
assign itch_stock_directory_short_sale_threshold_indicator_o = data_q[LEN*30+LEN*1-1:LEN*30];
assign itch_stock_directory_ipo_flag_o = data_q[LEN*31+LEN*1-1:LEN*31];
assign itch_stock_directory_luld_reference_price_tier_o = data_q[LEN*32+LEN*1-1:LEN*32];
assign itch_stock_directory_etp_flag_o = data_q[LEN*33+LEN*1-1:LEN*33];
assign itch_stock_directory_etp_leverage_factor_o = data_q[LEN*34+LEN*4-1:LEN*34];
assign itch_stock_directory_inverse_indicator_o = data_q[LEN*38+LEN*1-1:LEN*38];

assign itch_stock_trading_action_v_o = (itch_msg_type == 'd72) & (data_cnt_q == 'd4);
assign itch_stock_trading_action_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_stock_trading_action_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_stock_trading_action_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_stock_trading_action_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_stock_trading_action_trading_state_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_stock_trading_action_reserved_o = data_q[LEN*20+LEN*1-1:LEN*20];
assign itch_stock_trading_action_reason_o = data_q[LEN*21+LEN*4-1:LEN*21];

assign itch_reg_sho_restriction_v_o = (itch_msg_type == 'd89) & (data_cnt_q == 'd3);
assign itch_reg_sho_restriction_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_reg_sho_restriction_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_reg_sho_restriction_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_reg_sho_restriction_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_reg_sho_restriction_reg_sho_action_o = data_q[LEN*19+LEN*1-1:LEN*19];

assign itch_market_participant_position_v_o = (itch_msg_type == 'd76) & (data_cnt_q == 'd4);
assign itch_market_participant_position_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_market_participant_position_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_market_participant_position_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_market_participant_position_mpid_o = data_q[LEN*11+LEN*4-1:LEN*11];
assign itch_market_participant_position_stock_o = data_q[LEN*15+LEN*8-1:LEN*15];
assign itch_market_participant_position_primary_market_maker_o = data_q[LEN*23+LEN*1-1:LEN*23];
assign itch_market_participant_position_market_maker_mode_o = data_q[LEN*24+LEN*1-1:LEN*24];
assign itch_market_participant_position_market_participant_state_o = data_q[LEN*25+LEN*1-1:LEN*25];

assign itch_mwcb_decline_level_v_o = (itch_msg_type == 'd86) & (data_cnt_q == 'd5);
assign itch_mwcb_decline_level_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_mwcb_decline_level_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_mwcb_decline_level_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_mwcb_decline_level_level_1_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_mwcb_decline_level_level_2_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_mwcb_decline_level_level_3_o = data_q[LEN*27+LEN*8-1:LEN*27];

assign itch_mwcb_status_v_o = (itch_msg_type == 'd87) & (data_cnt_q == 'd2);
assign itch_mwcb_status_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_mwcb_status_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_mwcb_status_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_mwcb_status_breached_level_o = data_q[LEN*11+LEN*1-1:LEN*11];

assign itch_ipo_quoting_period_update_v_o = (itch_msg_type == 'd75) & (data_cnt_q == 'd4);
assign itch_ipo_quoting_period_update_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_ipo_quoting_period_update_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_ipo_quoting_period_update_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_ipo_quoting_period_update_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_ipo_quoting_period_update_ipo_quotation_release_time_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o = data_q[LEN*23+LEN*1-1:LEN*23];
assign itch_ipo_quoting_period_update_ipo_price_o = data_q[LEN*24+LEN*4-1:LEN*24];

assign itch_luld_auction_collar_v_o = (itch_msg_type == 'd74) & (data_cnt_q == 'd5);
assign itch_luld_auction_collar_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_luld_auction_collar_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_luld_auction_collar_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_luld_auction_collar_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_luld_auction_collar_auction_collar_reference_price_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_luld_auction_collar_upper_auction_collar_price_o = data_q[LEN*23+LEN*4-1:LEN*23];
assign itch_luld_auction_collar_lower_auction_collar_price_o = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_luld_auction_collar_auction_collar_extension_o = data_q[LEN*31+LEN*4-1:LEN*31];

assign itch_operational_halt_v_o = (itch_msg_type == 'd104) & (data_cnt_q == 'd3);
assign itch_operational_halt_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_operational_halt_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_operational_halt_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_operational_halt_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_operational_halt_market_code_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_operational_halt_operational_halt_action_o = data_q[LEN*20+LEN*1-1:LEN*20];

assign itch_add_order_v_o = (itch_msg_type == 'd65) & (data_cnt_q == 'd5);
assign itch_add_order_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_add_order_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_add_order_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_add_order_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_add_order_buy_sell_indicator_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_add_order_shares_o = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_add_order_stock_o = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_add_order_price_o = data_q[LEN*32+LEN*4-1:LEN*32];

assign itch_add_order_with_mpid_v_o = (itch_msg_type == 'd70) & (data_cnt_q == 'd5);
assign itch_add_order_with_mpid_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_add_order_with_mpid_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_add_order_with_mpid_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_add_order_with_mpid_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_add_order_with_mpid_buy_sell_indicator_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_add_order_with_mpid_shares_o = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_add_order_with_mpid_stock_o = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_add_order_with_mpid_price_o = data_q[LEN*32+LEN*4-1:LEN*32];
assign itch_add_order_with_mpid_attribution_o = data_q[LEN*36+LEN*4-1:LEN*36];

assign itch_order_executed_v_o = (itch_msg_type == 'd69) & (data_cnt_q == 'd4);
assign itch_order_executed_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_executed_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_executed_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_executed_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_executed_executed_shares_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_order_executed_match_number_o = data_q[LEN*23+LEN*8-1:LEN*23];

assign itch_order_executed_with_price_v_o = (itch_msg_type == 'd67) & (data_cnt_q == 'd5);
assign itch_order_executed_with_price_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_executed_with_price_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_executed_with_price_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_executed_with_price_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_executed_with_price_executed_shares_o = data_q[LEN*19+LEN*4-1:LEN*19];
assign itch_order_executed_with_price_match_number_o = data_q[LEN*23+LEN*8-1:LEN*23];
assign itch_order_executed_with_price_printable_o = data_q[LEN*31+LEN*1-1:LEN*31];
assign itch_order_executed_with_price_execution_price_o = data_q[LEN*32+LEN*4-1:LEN*32];

assign itch_order_cancel_v_o = (itch_msg_type == 'd88) & (data_cnt_q == 'd3);
assign itch_order_cancel_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_cancel_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_cancel_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_cancel_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_cancel_cancelled_shares_o = data_q[LEN*19+LEN*4-1:LEN*19];

assign itch_order_delete_v_o = (itch_msg_type == 'd68) & (data_cnt_q == 'd3);
assign itch_order_delete_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_delete_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_delete_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_delete_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];

assign itch_order_replace_v_o = (itch_msg_type == 'd85) & (data_cnt_q == 'd5);
assign itch_order_replace_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_order_replace_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_order_replace_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_order_replace_original_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_order_replace_new_order_reference_number_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_order_replace_shares_o = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_order_replace_price_o = data_q[LEN*31+LEN*4-1:LEN*31];

assign itch_trade_v_o = (itch_msg_type == 'd80) & (data_cnt_q == 'd6);
assign itch_trade_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_trade_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_trade_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_trade_order_reference_number_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_trade_buy_sell_indicator_o = data_q[LEN*19+LEN*1-1:LEN*19];
assign itch_trade_shares_o = data_q[LEN*20+LEN*4-1:LEN*20];
assign itch_trade_stock_o = data_q[LEN*24+LEN*8-1:LEN*24];
assign itch_trade_price_o = data_q[LEN*32+LEN*4-1:LEN*32];
assign itch_trade_match_number_o = data_q[LEN*36+LEN*8-1:LEN*36];

assign itch_cross_trade_v_o = (itch_msg_type == 'd81) & (data_cnt_q == 'd5);
assign itch_cross_trade_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_cross_trade_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_cross_trade_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_cross_trade_shares_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_cross_trade_stock_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_cross_trade_cross_price_o = data_q[LEN*27+LEN*4-1:LEN*27];
assign itch_cross_trade_match_number_o = data_q[LEN*31+LEN*8-1:LEN*31];
assign itch_cross_trade_cross_type_o = data_q[LEN*39+LEN*1-1:LEN*39];

assign itch_broken_trade_v_o = (itch_msg_type == 'd66) & (data_cnt_q == 'd3);
assign itch_broken_trade_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_broken_trade_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_broken_trade_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_broken_trade_match_number_o = data_q[LEN*11+LEN*8-1:LEN*11];

assign itch_net_order_imbalance_indicator_v_o = (itch_msg_type == 'd73) & (data_cnt_q == 'd7);
assign itch_net_order_imbalance_indicator_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_net_order_imbalance_indicator_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_net_order_imbalance_indicator_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_net_order_imbalance_indicator_paired_shares_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_net_order_imbalance_indicator_imbalance_shares_o = data_q[LEN*19+LEN*8-1:LEN*19];
assign itch_net_order_imbalance_indicator_imbalance_direction_o = data_q[LEN*27+LEN*1-1:LEN*27];
assign itch_net_order_imbalance_indicator_stock_o = data_q[LEN*28+LEN*8-1:LEN*28];
assign itch_net_order_imbalance_indicator_far_price_o = data_q[LEN*36+LEN*4-1:LEN*36];
assign itch_net_order_imbalance_indicator_near_price_o = data_q[LEN*40+LEN*4-1:LEN*40];
assign itch_net_order_imbalance_indicator_current_reference_price_o = data_q[LEN*44+LEN*4-1:LEN*44];
assign itch_net_order_imbalance_indicator_cross_type_o = data_q[LEN*48+LEN*1-1:LEN*48];
assign itch_net_order_imbalance_indicator_price_variation_indicator_o = data_q[LEN*49+LEN*1-1:LEN*49];

assign itch_retail_price_improvement_indicator_v_o = (itch_msg_type == 'd78) & (data_cnt_q == 'd3);
assign itch_retail_price_improvement_indicator_stock_locate_o = data_q[LEN*1+LEN*2-1:LEN*1];
assign itch_retail_price_improvement_indicator_tracking_number_o = data_q[LEN*3+LEN*2-1:LEN*3];
assign itch_retail_price_improvement_indicator_timestamp_o = data_q[LEN*5+LEN*6-1:LEN*5];
assign itch_retail_price_improvement_indicator_stock_o = data_q[LEN*11+LEN*8-1:LEN*11];
assign itch_retail_price_improvement_indicator_interest_flag_o = data_q[LEN*19+LEN*1-1:LEN*19];

assign itch_end_of_snapshot_v_o = (itch_msg_type == 'd71) & (data_cnt_q == 'd3);
assign itch_end_of_snapshot_sequence_number_o = data_q[LEN*1+LEN*20-1:LEN*1];
