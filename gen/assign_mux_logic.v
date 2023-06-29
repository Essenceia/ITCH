
assign itch_system_event_v_o = |dec_system_event_v_i;
assign itch_system_event_stock_locate_o = {2*LEN{dec_system_event_v_i[0]}} & dec_system_event_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_system_event_v_i[1]}} & dec_system_event_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_system_event_tracking_number_o = {2*LEN{dec_system_event_v_i[0]}} & dec_system_event_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_system_event_v_i[1]}} & dec_system_event_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_system_event_timestamp_o = {6*LEN{dec_system_event_v_i[0]}} & dec_system_event_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_system_event_v_i[1]}} & dec_system_event_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_system_event_event_code_o = {1*LEN{dec_system_event_v_i[0]}} & dec_system_event_event_code_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_system_event_v_i[1]}} & dec_system_event_event_code_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_stock_directory_v_o = |dec_stock_directory_v_i;
assign itch_stock_directory_stock_locate_o = {2*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_stock_directory_tracking_number_o = {2*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_stock_directory_timestamp_o = {6*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_stock_directory_stock_o = {8*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_stock_directory_market_category_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_market_category_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_market_category_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_financial_status_indicator_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_financial_status_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_financial_status_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_round_lot_size_o = {4*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_round_lot_size_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_round_lot_size_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_stock_directory_round_lots_only_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_round_lots_only_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_round_lots_only_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_issue_classification_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_issue_classification_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_issue_classification_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_issue_sub_type_o = {2*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_issue_sub_type_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_issue_sub_type_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_stock_directory_authenticity_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_authenticity_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_authenticity_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_short_sale_threshold_indicator_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_short_sale_threshold_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_short_sale_threshold_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_ipo_flag_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_ipo_flag_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_ipo_flag_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_luld_reference_price_tier_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_luld_reference_price_tier_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_luld_reference_price_tier_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_etp_flag_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_etp_flag_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_etp_flag_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_directory_etp_leverage_factor_o = {4*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_etp_leverage_factor_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_etp_leverage_factor_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_stock_directory_inverse_indicator_o = {1*LEN{dec_stock_directory_v_i[0]}} & dec_stock_directory_inverse_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_directory_v_i[1]}} & dec_stock_directory_inverse_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_stock_trading_action_v_o = |dec_stock_trading_action_v_i;
assign itch_stock_trading_action_stock_locate_o = {2*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_stock_trading_action_tracking_number_o = {2*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_stock_trading_action_timestamp_o = {6*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_stock_trading_action_stock_o = {8*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_stock_trading_action_trading_state_o = {1*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_trading_state_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_trading_state_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_trading_action_reserved_o = {1*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_reserved_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_reserved_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_stock_trading_action_reason_o = {4*LEN{dec_stock_trading_action_v_i[0]}} & dec_stock_trading_action_reason_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_stock_trading_action_v_i[1]}} & dec_stock_trading_action_reason_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_reg_sho_restriction_v_o = |dec_reg_sho_restriction_v_i;
assign itch_reg_sho_restriction_stock_locate_o = {2*LEN{dec_reg_sho_restriction_v_i[0]}} & dec_reg_sho_restriction_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_reg_sho_restriction_v_i[1]}} & dec_reg_sho_restriction_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_reg_sho_restriction_tracking_number_o = {2*LEN{dec_reg_sho_restriction_v_i[0]}} & dec_reg_sho_restriction_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_reg_sho_restriction_v_i[1]}} & dec_reg_sho_restriction_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_reg_sho_restriction_timestamp_o = {6*LEN{dec_reg_sho_restriction_v_i[0]}} & dec_reg_sho_restriction_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_reg_sho_restriction_v_i[1]}} & dec_reg_sho_restriction_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_reg_sho_restriction_stock_o = {8*LEN{dec_reg_sho_restriction_v_i[0]}} & dec_reg_sho_restriction_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_reg_sho_restriction_v_i[1]}} & dec_reg_sho_restriction_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_reg_sho_restriction_reg_sho_action_o = {1*LEN{dec_reg_sho_restriction_v_i[0]}} & dec_reg_sho_restriction_reg_sho_action_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_reg_sho_restriction_v_i[1]}} & dec_reg_sho_restriction_reg_sho_action_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_market_participant_position_v_o = |dec_market_participant_position_v_i;
assign itch_market_participant_position_stock_locate_o = {2*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_market_participant_position_tracking_number_o = {2*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_market_participant_position_timestamp_o = {6*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_market_participant_position_mpid_o = {4*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_mpid_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_mpid_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_market_participant_position_stock_o = {8*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_market_participant_position_primary_market_maker_o = {1*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_primary_market_maker_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_primary_market_maker_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_market_participant_position_market_maker_mode_o = {1*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_market_maker_mode_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_market_maker_mode_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_market_participant_position_market_participant_state_o = {1*LEN{dec_market_participant_position_v_i[0]}} & dec_market_participant_position_market_participant_state_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_market_participant_position_v_i[1]}} & dec_market_participant_position_market_participant_state_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_mwcb_decline_level_v_o = |dec_mwcb_decline_level_v_i;
assign itch_mwcb_decline_level_stock_locate_o = {2*LEN{dec_mwcb_decline_level_v_i[0]}} & dec_mwcb_decline_level_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_mwcb_decline_level_v_i[1]}} & dec_mwcb_decline_level_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_mwcb_decline_level_tracking_number_o = {2*LEN{dec_mwcb_decline_level_v_i[0]}} & dec_mwcb_decline_level_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_mwcb_decline_level_v_i[1]}} & dec_mwcb_decline_level_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_mwcb_decline_level_timestamp_o = {6*LEN{dec_mwcb_decline_level_v_i[0]}} & dec_mwcb_decline_level_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_mwcb_decline_level_v_i[1]}} & dec_mwcb_decline_level_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_mwcb_decline_level_level_1_o = {8*LEN{dec_mwcb_decline_level_v_i[0]}} & dec_mwcb_decline_level_level_1_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_mwcb_decline_level_v_i[1]}} & dec_mwcb_decline_level_level_1_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_mwcb_decline_level_level_2_o = {8*LEN{dec_mwcb_decline_level_v_i[0]}} & dec_mwcb_decline_level_level_2_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_mwcb_decline_level_v_i[1]}} & dec_mwcb_decline_level_level_2_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_mwcb_decline_level_level_3_o = {8*LEN{dec_mwcb_decline_level_v_i[0]}} & dec_mwcb_decline_level_level_3_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_mwcb_decline_level_v_i[1]}} & dec_mwcb_decline_level_level_3_i[1*8*LEN+8*LEN-1:1*8*LEN];

assign itch_mwcb_status_v_o = |dec_mwcb_status_v_i;
assign itch_mwcb_status_stock_locate_o = {2*LEN{dec_mwcb_status_v_i[0]}} & dec_mwcb_status_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_mwcb_status_v_i[1]}} & dec_mwcb_status_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_mwcb_status_tracking_number_o = {2*LEN{dec_mwcb_status_v_i[0]}} & dec_mwcb_status_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_mwcb_status_v_i[1]}} & dec_mwcb_status_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_mwcb_status_timestamp_o = {6*LEN{dec_mwcb_status_v_i[0]}} & dec_mwcb_status_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_mwcb_status_v_i[1]}} & dec_mwcb_status_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_mwcb_status_breached_level_o = {1*LEN{dec_mwcb_status_v_i[0]}} & dec_mwcb_status_breached_level_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_mwcb_status_v_i[1]}} & dec_mwcb_status_breached_level_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_ipo_quoting_period_update_v_o = |dec_ipo_quoting_period_update_v_i;
assign itch_ipo_quoting_period_update_stock_locate_o = {2*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_ipo_quoting_period_update_tracking_number_o = {2*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_ipo_quoting_period_update_timestamp_o = {6*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_ipo_quoting_period_update_stock_o = {8*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_ipo_quoting_period_update_ipo_quotation_release_time_o = {4*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_ipo_quotation_release_time_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_ipo_quotation_release_time_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_ipo_quoting_period_update_ipo_quotation_release_qualifier_o = {1*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_ipo_quotation_release_qualifier_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_ipo_quotation_release_qualifier_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_ipo_quoting_period_update_ipo_price_o = {4*LEN{dec_ipo_quoting_period_update_v_i[0]}} & dec_ipo_quoting_period_update_ipo_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_ipo_quoting_period_update_v_i[1]}} & dec_ipo_quoting_period_update_ipo_price_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_luld_auction_collar_v_o = |dec_luld_auction_collar_v_i;
assign itch_luld_auction_collar_stock_locate_o = {2*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_luld_auction_collar_tracking_number_o = {2*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_luld_auction_collar_timestamp_o = {6*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_luld_auction_collar_stock_o = {8*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_luld_auction_collar_auction_collar_reference_price_o = {4*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_auction_collar_reference_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_auction_collar_reference_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_luld_auction_collar_upper_auction_collar_price_o = {4*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_upper_auction_collar_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_upper_auction_collar_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_luld_auction_collar_lower_auction_collar_price_o = {4*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_lower_auction_collar_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_lower_auction_collar_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_luld_auction_collar_auction_collar_extension_o = {4*LEN{dec_luld_auction_collar_v_i[0]}} & dec_luld_auction_collar_auction_collar_extension_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_luld_auction_collar_v_i[1]}} & dec_luld_auction_collar_auction_collar_extension_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_operational_halt_v_o = |dec_operational_halt_v_i;
assign itch_operational_halt_stock_locate_o = {2*LEN{dec_operational_halt_v_i[0]}} & dec_operational_halt_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_operational_halt_v_i[1]}} & dec_operational_halt_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_operational_halt_tracking_number_o = {2*LEN{dec_operational_halt_v_i[0]}} & dec_operational_halt_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_operational_halt_v_i[1]}} & dec_operational_halt_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_operational_halt_timestamp_o = {6*LEN{dec_operational_halt_v_i[0]}} & dec_operational_halt_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_operational_halt_v_i[1]}} & dec_operational_halt_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_operational_halt_stock_o = {8*LEN{dec_operational_halt_v_i[0]}} & dec_operational_halt_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_operational_halt_v_i[1]}} & dec_operational_halt_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_operational_halt_market_code_o = {1*LEN{dec_operational_halt_v_i[0]}} & dec_operational_halt_market_code_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_operational_halt_v_i[1]}} & dec_operational_halt_market_code_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_operational_halt_operational_halt_action_o = {1*LEN{dec_operational_halt_v_i[0]}} & dec_operational_halt_operational_halt_action_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_operational_halt_v_i[1]}} & dec_operational_halt_operational_halt_action_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_add_order_v_o = |dec_add_order_v_i;
assign itch_add_order_stock_locate_o = {2*LEN{dec_add_order_v_i[0]}} & dec_add_order_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_add_order_v_i[1]}} & dec_add_order_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_add_order_tracking_number_o = {2*LEN{dec_add_order_v_i[0]}} & dec_add_order_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_add_order_v_i[1]}} & dec_add_order_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_add_order_timestamp_o = {6*LEN{dec_add_order_v_i[0]}} & dec_add_order_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_add_order_v_i[1]}} & dec_add_order_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_add_order_order_reference_number_o = {8*LEN{dec_add_order_v_i[0]}} & dec_add_order_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_add_order_v_i[1]}} & dec_add_order_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_add_order_buy_sell_indicator_o = {1*LEN{dec_add_order_v_i[0]}} & dec_add_order_buy_sell_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_add_order_v_i[1]}} & dec_add_order_buy_sell_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_add_order_shares_o = {4*LEN{dec_add_order_v_i[0]}} & dec_add_order_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_add_order_v_i[1]}} & dec_add_order_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_add_order_stock_o = {8*LEN{dec_add_order_v_i[0]}} & dec_add_order_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_add_order_v_i[1]}} & dec_add_order_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_add_order_price_o = {4*LEN{dec_add_order_v_i[0]}} & dec_add_order_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_add_order_v_i[1]}} & dec_add_order_price_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_add_order_with_mpid_v_o = |dec_add_order_with_mpid_v_i;
assign itch_add_order_with_mpid_stock_locate_o = {2*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_add_order_with_mpid_tracking_number_o = {2*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_add_order_with_mpid_timestamp_o = {6*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_add_order_with_mpid_order_reference_number_o = {8*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_add_order_with_mpid_buy_sell_indicator_o = {1*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_buy_sell_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_buy_sell_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_add_order_with_mpid_shares_o = {4*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_add_order_with_mpid_stock_o = {8*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_add_order_with_mpid_price_o = {4*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_add_order_with_mpid_attribution_o = {4*LEN{dec_add_order_with_mpid_v_i[0]}} & dec_add_order_with_mpid_attribution_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_add_order_with_mpid_v_i[1]}} & dec_add_order_with_mpid_attribution_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_order_executed_v_o = |dec_order_executed_v_i;
assign itch_order_executed_stock_locate_o = {2*LEN{dec_order_executed_v_i[0]}} & dec_order_executed_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_executed_v_i[1]}} & dec_order_executed_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_executed_tracking_number_o = {2*LEN{dec_order_executed_v_i[0]}} & dec_order_executed_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_executed_v_i[1]}} & dec_order_executed_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_executed_timestamp_o = {6*LEN{dec_order_executed_v_i[0]}} & dec_order_executed_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_order_executed_v_i[1]}} & dec_order_executed_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_order_executed_order_reference_number_o = {8*LEN{dec_order_executed_v_i[0]}} & dec_order_executed_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_executed_v_i[1]}} & dec_order_executed_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_order_executed_executed_shares_o = {4*LEN{dec_order_executed_v_i[0]}} & dec_order_executed_executed_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_order_executed_v_i[1]}} & dec_order_executed_executed_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_order_executed_match_number_o = {8*LEN{dec_order_executed_v_i[0]}} & dec_order_executed_match_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_executed_v_i[1]}} & dec_order_executed_match_number_i[1*8*LEN+8*LEN-1:1*8*LEN];

assign itch_order_executed_with_price_v_o = |dec_order_executed_with_price_v_i;
assign itch_order_executed_with_price_stock_locate_o = {2*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_executed_with_price_tracking_number_o = {2*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_executed_with_price_timestamp_o = {6*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_order_executed_with_price_order_reference_number_o = {8*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_order_executed_with_price_executed_shares_o = {4*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_executed_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_executed_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_order_executed_with_price_match_number_o = {8*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_match_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_match_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_order_executed_with_price_printable_o = {1*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_printable_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_printable_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_order_executed_with_price_execution_price_o = {4*LEN{dec_order_executed_with_price_v_i[0]}} & dec_order_executed_with_price_execution_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_order_executed_with_price_v_i[1]}} & dec_order_executed_with_price_execution_price_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_order_cancel_v_o = |dec_order_cancel_v_i;
assign itch_order_cancel_stock_locate_o = {2*LEN{dec_order_cancel_v_i[0]}} & dec_order_cancel_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_cancel_v_i[1]}} & dec_order_cancel_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_cancel_tracking_number_o = {2*LEN{dec_order_cancel_v_i[0]}} & dec_order_cancel_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_cancel_v_i[1]}} & dec_order_cancel_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_cancel_timestamp_o = {6*LEN{dec_order_cancel_v_i[0]}} & dec_order_cancel_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_order_cancel_v_i[1]}} & dec_order_cancel_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_order_cancel_order_reference_number_o = {8*LEN{dec_order_cancel_v_i[0]}} & dec_order_cancel_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_cancel_v_i[1]}} & dec_order_cancel_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_order_cancel_cancelled_shares_o = {4*LEN{dec_order_cancel_v_i[0]}} & dec_order_cancel_cancelled_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_order_cancel_v_i[1]}} & dec_order_cancel_cancelled_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_order_delete_v_o = |dec_order_delete_v_i;
assign itch_order_delete_stock_locate_o = {2*LEN{dec_order_delete_v_i[0]}} & dec_order_delete_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_delete_v_i[1]}} & dec_order_delete_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_delete_tracking_number_o = {2*LEN{dec_order_delete_v_i[0]}} & dec_order_delete_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_delete_v_i[1]}} & dec_order_delete_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_delete_timestamp_o = {6*LEN{dec_order_delete_v_i[0]}} & dec_order_delete_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_order_delete_v_i[1]}} & dec_order_delete_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_order_delete_order_reference_number_o = {8*LEN{dec_order_delete_v_i[0]}} & dec_order_delete_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_delete_v_i[1]}} & dec_order_delete_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];

assign itch_order_replace_v_o = |dec_order_replace_v_i;
assign itch_order_replace_stock_locate_o = {2*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_replace_tracking_number_o = {2*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_order_replace_timestamp_o = {6*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_order_replace_original_order_reference_number_o = {8*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_original_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_original_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_order_replace_new_order_reference_number_o = {8*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_new_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_new_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_order_replace_shares_o = {4*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_order_replace_price_o = {4*LEN{dec_order_replace_v_i[0]}} & dec_order_replace_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_order_replace_v_i[1]}} & dec_order_replace_price_i[1*4*LEN+4*LEN-1:1*4*LEN];

assign itch_trade_v_o = |dec_trade_v_i;
assign itch_trade_stock_locate_o = {2*LEN{dec_trade_v_i[0]}} & dec_trade_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_trade_v_i[1]}} & dec_trade_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_trade_tracking_number_o = {2*LEN{dec_trade_v_i[0]}} & dec_trade_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_trade_v_i[1]}} & dec_trade_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_trade_timestamp_o = {6*LEN{dec_trade_v_i[0]}} & dec_trade_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_trade_v_i[1]}} & dec_trade_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_trade_order_reference_number_o = {8*LEN{dec_trade_v_i[0]}} & dec_trade_order_reference_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_trade_v_i[1]}} & dec_trade_order_reference_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_trade_buy_sell_indicator_o = {1*LEN{dec_trade_v_i[0]}} & dec_trade_buy_sell_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_trade_v_i[1]}} & dec_trade_buy_sell_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_trade_shares_o = {4*LEN{dec_trade_v_i[0]}} & dec_trade_shares_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_trade_v_i[1]}} & dec_trade_shares_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_trade_stock_o = {8*LEN{dec_trade_v_i[0]}} & dec_trade_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_trade_v_i[1]}} & dec_trade_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_trade_price_o = {4*LEN{dec_trade_v_i[0]}} & dec_trade_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_trade_v_i[1]}} & dec_trade_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_trade_match_number_o = {8*LEN{dec_trade_v_i[0]}} & dec_trade_match_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_trade_v_i[1]}} & dec_trade_match_number_i[1*8*LEN+8*LEN-1:1*8*LEN];

assign itch_cross_trade_v_o = |dec_cross_trade_v_i;
assign itch_cross_trade_stock_locate_o = {2*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_cross_trade_tracking_number_o = {2*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_cross_trade_timestamp_o = {6*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_cross_trade_shares_o = {8*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_shares_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_shares_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_cross_trade_stock_o = {8*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_cross_trade_cross_price_o = {4*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_cross_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_cross_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_cross_trade_match_number_o = {8*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_match_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_match_number_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_cross_trade_cross_type_o = {1*LEN{dec_cross_trade_v_i[0]}} & dec_cross_trade_cross_type_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_cross_trade_v_i[1]}} & dec_cross_trade_cross_type_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_broken_trade_v_o = |dec_broken_trade_v_i;
assign itch_broken_trade_stock_locate_o = {2*LEN{dec_broken_trade_v_i[0]}} & dec_broken_trade_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_broken_trade_v_i[1]}} & dec_broken_trade_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_broken_trade_tracking_number_o = {2*LEN{dec_broken_trade_v_i[0]}} & dec_broken_trade_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_broken_trade_v_i[1]}} & dec_broken_trade_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_broken_trade_timestamp_o = {6*LEN{dec_broken_trade_v_i[0]}} & dec_broken_trade_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_broken_trade_v_i[1]}} & dec_broken_trade_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_broken_trade_match_number_o = {8*LEN{dec_broken_trade_v_i[0]}} & dec_broken_trade_match_number_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_broken_trade_v_i[1]}} & dec_broken_trade_match_number_i[1*8*LEN+8*LEN-1:1*8*LEN];

assign itch_net_order_imbalance_indicator_v_o = |dec_net_order_imbalance_indicator_v_i;
assign itch_net_order_imbalance_indicator_stock_locate_o = {2*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_net_order_imbalance_indicator_tracking_number_o = {2*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_net_order_imbalance_indicator_timestamp_o = {6*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_net_order_imbalance_indicator_paired_shares_o = {8*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_paired_shares_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_paired_shares_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_net_order_imbalance_indicator_imbalance_shares_o = {8*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_imbalance_shares_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_imbalance_shares_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_net_order_imbalance_indicator_imbalance_direction_o = {1*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_imbalance_direction_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_imbalance_direction_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_net_order_imbalance_indicator_stock_o = {8*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_net_order_imbalance_indicator_far_price_o = {4*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_far_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_far_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_net_order_imbalance_indicator_near_price_o = {4*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_near_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_near_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_net_order_imbalance_indicator_current_reference_price_o = {4*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_current_reference_price_i[0*4*LEN+4*LEN-1:0*4*LEN]
|{4*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_current_reference_price_i[1*4*LEN+4*LEN-1:1*4*LEN];
assign itch_net_order_imbalance_indicator_cross_type_o = {1*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_cross_type_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_cross_type_i[1*1*LEN+1*LEN-1:1*1*LEN];
assign itch_net_order_imbalance_indicator_price_variation_indicator_o = {1*LEN{dec_net_order_imbalance_indicator_v_i[0]}} & dec_net_order_imbalance_indicator_price_variation_indicator_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_net_order_imbalance_indicator_v_i[1]}} & dec_net_order_imbalance_indicator_price_variation_indicator_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_retail_price_improvement_indicator_v_o = |dec_retail_price_improvement_indicator_v_i;
assign itch_retail_price_improvement_indicator_stock_locate_o = {2*LEN{dec_retail_price_improvement_indicator_v_i[0]}} & dec_retail_price_improvement_indicator_stock_locate_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_retail_price_improvement_indicator_v_i[1]}} & dec_retail_price_improvement_indicator_stock_locate_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_retail_price_improvement_indicator_tracking_number_o = {2*LEN{dec_retail_price_improvement_indicator_v_i[0]}} & dec_retail_price_improvement_indicator_tracking_number_i[0*2*LEN+2*LEN-1:0*2*LEN]
|{2*LEN{dec_retail_price_improvement_indicator_v_i[1]}} & dec_retail_price_improvement_indicator_tracking_number_i[1*2*LEN+2*LEN-1:1*2*LEN];
assign itch_retail_price_improvement_indicator_timestamp_o = {6*LEN{dec_retail_price_improvement_indicator_v_i[0]}} & dec_retail_price_improvement_indicator_timestamp_i[0*6*LEN+6*LEN-1:0*6*LEN]
|{6*LEN{dec_retail_price_improvement_indicator_v_i[1]}} & dec_retail_price_improvement_indicator_timestamp_i[1*6*LEN+6*LEN-1:1*6*LEN];
assign itch_retail_price_improvement_indicator_stock_o = {8*LEN{dec_retail_price_improvement_indicator_v_i[0]}} & dec_retail_price_improvement_indicator_stock_i[0*8*LEN+8*LEN-1:0*8*LEN]
|{8*LEN{dec_retail_price_improvement_indicator_v_i[1]}} & dec_retail_price_improvement_indicator_stock_i[1*8*LEN+8*LEN-1:1*8*LEN];
assign itch_retail_price_improvement_indicator_interest_flag_o = {1*LEN{dec_retail_price_improvement_indicator_v_i[0]}} & dec_retail_price_improvement_indicator_interest_flag_i[0*1*LEN+1*LEN-1:0*1*LEN]
|{1*LEN{dec_retail_price_improvement_indicator_v_i[1]}} & dec_retail_price_improvement_indicator_interest_flag_i[1*1*LEN+1*LEN-1:1*1*LEN];

assign itch_end_of_snapshot_v_o = |dec_end_of_snapshot_v_i;
assign itch_end_of_snapshot_sequence_number_o = {20*LEN{dec_end_of_snapshot_v_i[0]}} & dec_end_of_snapshot_sequence_number_i[0*20*LEN+20*LEN-1:0*20*LEN]
|{20*LEN{dec_end_of_snapshot_v_i[1]}} & dec_end_of_snapshot_sequence_number_i[1*20*LEN+20*LEN-1:1*20*LEN];
