
logic system_event_v;
logic [2*LEN-1:0] system_event_stock_locate;
logic [2*LEN-1:0] system_event_tracking_number;
logic [6*LEN-1:0] system_event_timestamp;
logic [1*LEN-1:0] system_event_event_code;

logic stock_directory_v;
logic [2*LEN-1:0] stock_directory_stock_locate;
logic [2*LEN-1:0] stock_directory_tracking_number;
logic [6*LEN-1:0] stock_directory_timestamp;
logic [8*LEN-1:0] stock_directory_stock;
logic [1*LEN-1:0] stock_directory_market_category;
logic [1*LEN-1:0] stock_directory_financial_status_indicator;
logic [4*LEN-1:0] stock_directory_round_lot_size;
logic [1*LEN-1:0] stock_directory_round_lots_only;
logic [1*LEN-1:0] stock_directory_issue_classification;
logic [2*LEN-1:0] stock_directory_issue_sub_type;
logic [1*LEN-1:0] stock_directory_authenticity;
logic [1*LEN-1:0] stock_directory_short_sale_threshold_indicator;
logic [1*LEN-1:0] stock_directory_ipo_flag;
logic [1*LEN-1:0] stock_directory_luld_reference_price_tier;
logic [1*LEN-1:0] stock_directory_etp_flag;
logic [4*LEN-1:0] stock_directory_etp_leverage_factor;
logic [1*LEN-1:0] stock_directory_inverse_indicator;

logic stock_trading_action_v;
logic [2*LEN-1:0] stock_trading_action_stock_locate;
logic [2*LEN-1:0] stock_trading_action_tracking_number;
logic [6*LEN-1:0] stock_trading_action_timestamp;
logic [8*LEN-1:0] stock_trading_action_stock;
logic [1*LEN-1:0] stock_trading_action_trading_state;
logic [1*LEN-1:0] stock_trading_action_reserved;
logic [4*LEN-1:0] stock_trading_action_reason;

logic reg_sho_restriction_v;
logic [2*LEN-1:0] reg_sho_restriction_stock_locate;
logic [2*LEN-1:0] reg_sho_restriction_tracking_number;
logic [6*LEN-1:0] reg_sho_restriction_timestamp;
logic [8*LEN-1:0] reg_sho_restriction_stock;
logic [1*LEN-1:0] reg_sho_restriction_reg_sho_action;

logic market_participant_position_v;
logic [2*LEN-1:0] market_participant_position_stock_locate;
logic [2*LEN-1:0] market_participant_position_tracking_number;
logic [6*LEN-1:0] market_participant_position_timestamp;
logic [4*LEN-1:0] market_participant_position_mpid;
logic [8*LEN-1:0] market_participant_position_stock;
logic [1*LEN-1:0] market_participant_position_primary_market_maker;
logic [1*LEN-1:0] market_participant_position_market_maker_mode;
logic [1*LEN-1:0] market_participant_position_market_participant_state;

logic mwcb_decline_level_v;
logic [2*LEN-1:0] mwcb_decline_level_stock_locate;
logic [2*LEN-1:0] mwcb_decline_level_tracking_number;
logic [6*LEN-1:0] mwcb_decline_level_timestamp;
logic [8*LEN-1:0] mwcb_decline_level_level_1;
logic [8*LEN-1:0] mwcb_decline_level_level_2;
logic [8*LEN-1:0] mwcb_decline_level_level_3;

logic mwcb_status_v;
logic [2*LEN-1:0] mwcb_status_stock_locate;
logic [2*LEN-1:0] mwcb_status_tracking_number;
logic [6*LEN-1:0] mwcb_status_timestamp;
logic [1*LEN-1:0] mwcb_status_breached_level;

logic ipo_quoting_period_update_v;
logic [2*LEN-1:0] ipo_quoting_period_update_stock_locate;
logic [2*LEN-1:0] ipo_quoting_period_update_tracking_number;
logic [6*LEN-1:0] ipo_quoting_period_update_timestamp;
logic [8*LEN-1:0] ipo_quoting_period_update_stock;
logic [4*LEN-1:0] ipo_quoting_period_update_ipo_quotation_release_time;
logic [1*LEN-1:0] ipo_quoting_period_update_ipo_quotation_release_qualifier;
logic [4*LEN-1:0] ipo_quoting_period_update_ipo_price;

logic luld_auction_collar_v;
logic [2*LEN-1:0] luld_auction_collar_stock_locate;
logic [2*LEN-1:0] luld_auction_collar_tracking_number;
logic [6*LEN-1:0] luld_auction_collar_timestamp;
logic [8*LEN-1:0] luld_auction_collar_stock;
logic [4*LEN-1:0] luld_auction_collar_auction_collar_reference_price;
logic [4*LEN-1:0] luld_auction_collar_upper_auction_collar_price;
logic [4*LEN-1:0] luld_auction_collar_lower_auction_collar_price;
logic [4*LEN-1:0] luld_auction_collar_auction_collar_extension;

logic operational_halt_v;
logic [2*LEN-1:0] operational_halt_stock_locate;
logic [2*LEN-1:0] operational_halt_tracking_number;
logic [6*LEN-1:0] operational_halt_timestamp;
logic [8*LEN-1:0] operational_halt_stock;
logic [1*LEN-1:0] operational_halt_market_code;
logic [1*LEN-1:0] operational_halt_operational_halt_action;

logic add_order_v;
logic [2*LEN-1:0] add_order_stock_locate;
logic [2*LEN-1:0] add_order_tracking_number;
logic [6*LEN-1:0] add_order_timestamp;
logic [8*LEN-1:0] add_order_order_reference_number;
logic [1*LEN-1:0] add_order_buy_sell_indicator;
logic [4*LEN-1:0] add_order_shares;
logic [8*LEN-1:0] add_order_stock;
logic [4*LEN-1:0] add_order_price;

logic add_order_with_mpid_v;
logic [2*LEN-1:0] add_order_with_mpid_stock_locate;
logic [2*LEN-1:0] add_order_with_mpid_tracking_number;
logic [6*LEN-1:0] add_order_with_mpid_timestamp;
logic [8*LEN-1:0] add_order_with_mpid_order_reference_number;
logic [1*LEN-1:0] add_order_with_mpid_buy_sell_indicator;
logic [4*LEN-1:0] add_order_with_mpid_shares;
logic [8*LEN-1:0] add_order_with_mpid_stock;
logic [4*LEN-1:0] add_order_with_mpid_price;
logic [4*LEN-1:0] add_order_with_mpid_attribution;

logic order_executed_v;
logic [2*LEN-1:0] order_executed_stock_locate;
logic [2*LEN-1:0] order_executed_tracking_number;
logic [6*LEN-1:0] order_executed_timestamp;
logic [8*LEN-1:0] order_executed_order_reference_number;
logic [4*LEN-1:0] order_executed_executed_shares;
logic [8*LEN-1:0] order_executed_match_number;

logic order_executed_with_price_v;
logic [2*LEN-1:0] order_executed_with_price_stock_locate;
logic [2*LEN-1:0] order_executed_with_price_tracking_number;
logic [6*LEN-1:0] order_executed_with_price_timestamp;
logic [8*LEN-1:0] order_executed_with_price_order_reference_number;
logic [4*LEN-1:0] order_executed_with_price_executed_shares;
logic [8*LEN-1:0] order_executed_with_price_match_number;
logic [1*LEN-1:0] order_executed_with_price_printable;
logic [4*LEN-1:0] order_executed_with_price_execution_price;

logic order_cancel_v;
logic [2*LEN-1:0] order_cancel_stock_locate;
logic [2*LEN-1:0] order_cancel_tracking_number;
logic [6*LEN-1:0] order_cancel_timestamp;
logic [8*LEN-1:0] order_cancel_order_reference_number;
logic [4*LEN-1:0] order_cancel_cancelled_shares;

logic order_delete_v;
logic [2*LEN-1:0] order_delete_stock_locate;
logic [2*LEN-1:0] order_delete_tracking_number;
logic [6*LEN-1:0] order_delete_timestamp;
logic [8*LEN-1:0] order_delete_order_reference_number;

logic order_replace_v;
logic [2*LEN-1:0] order_replace_stock_locate;
logic [2*LEN-1:0] order_replace_tracking_number;
logic [6*LEN-1:0] order_replace_timestamp;
logic [8*LEN-1:0] order_replace_original_order_reference_number;
logic [8*LEN-1:0] order_replace_new_order_reference_number;
logic [4*LEN-1:0] order_replace_shares;
logic [4*LEN-1:0] order_replace_price;

logic trade_v;
logic [2*LEN-1:0] trade_stock_locate;
logic [2*LEN-1:0] trade_tracking_number;
logic [6*LEN-1:0] trade_timestamp;
logic [8*LEN-1:0] trade_order_reference_number;
logic [1*LEN-1:0] trade_buy_sell_indicator;
logic [4*LEN-1:0] trade_shares;
logic [8*LEN-1:0] trade_stock;
logic [4*LEN-1:0] trade_price;
logic [8*LEN-1:0] trade_match_number;

logic cross_trade_v;
logic [2*LEN-1:0] cross_trade_stock_locate;
logic [2*LEN-1:0] cross_trade_tracking_number;
logic [6*LEN-1:0] cross_trade_timestamp;
logic [8*LEN-1:0] cross_trade_shares;
logic [8*LEN-1:0] cross_trade_stock;
logic [4*LEN-1:0] cross_trade_cross_price;
logic [8*LEN-1:0] cross_trade_match_number;
logic [1*LEN-1:0] cross_trade_cross_type;

logic broken_trade_v;
logic [2*LEN-1:0] broken_trade_stock_locate;
logic [2*LEN-1:0] broken_trade_tracking_number;
logic [6*LEN-1:0] broken_trade_timestamp;
logic [8*LEN-1:0] broken_trade_match_number;

logic net_order_imbalance_indicator_v;
logic [2*LEN-1:0] net_order_imbalance_indicator_stock_locate;
logic [2*LEN-1:0] net_order_imbalance_indicator_tracking_number;
logic [6*LEN-1:0] net_order_imbalance_indicator_timestamp;
logic [8*LEN-1:0] net_order_imbalance_indicator_paired_shares;
logic [8*LEN-1:0] net_order_imbalance_indicator_imbalance_shares;
logic [1*LEN-1:0] net_order_imbalance_indicator_imbalance_direction;
logic [8*LEN-1:0] net_order_imbalance_indicator_stock;
logic [4*LEN-1:0] net_order_imbalance_indicator_far_price;
logic [4*LEN-1:0] net_order_imbalance_indicator_near_price;
logic [4*LEN-1:0] net_order_imbalance_indicator_current_reference_price;
logic [1*LEN-1:0] net_order_imbalance_indicator_cross_type;
logic [1*LEN-1:0] net_order_imbalance_indicator_price_variation_indicator;

logic retail_price_improvement_indicator_v;
logic [2*LEN-1:0] retail_price_improvement_indicator_stock_locate;
logic [2*LEN-1:0] retail_price_improvement_indicator_tracking_number;
logic [6*LEN-1:0] retail_price_improvement_indicator_timestamp;
logic [8*LEN-1:0] retail_price_improvement_indicator_stock;
logic [1*LEN-1:0] retail_price_improvement_indicator_interest_flag;

logic end_of_snapshot_v;
logic [20*LEN-1:0] end_of_snapshot_sequence_number;
