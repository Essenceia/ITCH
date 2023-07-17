# TotalView 5.0 ITCH decoder

RTL implementation of a Nasdaq TotalView-ITCH 5.0 decoder.

Designed to work alongside the MoldUPD64 module as part of a larger
[NASDAQ compatible HFT FPGA project](https://github.com/Essenceia/NASDAQ-HFT-FPGA.).

## Interface 

TotalView 5.0 itch top level interface : 

```
module tv_itch5 #(
	`ifdef DEBUG_ID
	parameter DEBUG_ID_W = 64,
	`endif
	// itch data
	parameter LEN = 8,

	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = AXI_DATA_W / 8,
	parameter KEEP_LW    = $clog2(AXI_KEEP_W) + 1,

	// overlap fields
	parameter OV_DATA_W  = 64-(2*LEN),//48
	parameter OV_KEEP_W  = (OV_DATA_W/8),//6
	parameter OV_KEEP_LW = 3, //$clog2(OV_KEEP_W+1),	

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
	input                  valid_i,
	input                  start_i,
	input [KEEP_LW-1:0]    len_i,
	input [AXI_DATA_W-1:0] data_i,
	// overlap message bits, only valid for first payload
	input                  ov_valid_i,
	input [OV_KEEP_LW-1:0] ov_len_i,
	input [OV_DATA_W-1:0]  ov_data_i,

    `ifdef EARLY
    [early ITCH decoded messages signals]
    `endif

    [ITCH decoded messages signals]
```

## Mold message data

Mold message data driven by moldudp64 module.

- `valid_i` : validity bit, mold message is currently getting transferred.

- `start_i` : start of a new mold message.

- `len_i`  : number of valid bytes in data.

- `data_i` : mold message data, aligned on 8 bytes.

## Overlap of mold message data

We call an overlap when data of 2 different mold messages are transferred within a same AXI
payload. Overlap valid only occurs on the beginning of a new message so `ov_valid_i` implies 
the start of a new mold message.

- `ov_valid_i` : validity bit, new overlap mold message has been identified.

- `ov_len_i`   : number of valid bytes in overlapping data.

- `ov_data_i`  : new overlapping mold message data, aligned on 8 bytes.

### Example 

An AXI payload has a width of 8 bytes and each character denotes a byte,
`A` are bytes belonging to the end of a mold message
`_` are the length bytes belonging to a new mold message
`B` are the bytes belonging to the data field of this new mold message

```
BB__AAAA
```

In this example there is an overlap, data bytes of this new mold message would be transmitted over
the overlap signals :

```
ov_valid  = 1'b1
ov_len_i  = 'd2
ov_data_i = XXXXBB

valid_i = 1'b1
start_i = 1'b0
len_i   = 'd4
data_i  = XXXXAAAA
```
## ( Optional ) Debug id

To help debugging, whenever the `DEBUG_ID` flag is set an new identification
number will be attacked to each message.

This is used to keep track of individual itch messages in the top level
test bench.

By default `DEBUG_ID` is not defined.

- `debug_id_i` : debug id tracking each new mold message, valid when `start_i` and 
    `valid_i` are set.

- `debug_id_o` : debug id of the decoded itch message, valid when any `itch_<message_type>_v_o`
    validity bit is set.

## ( Optional ) Early ITCH decoded message interface

The optional early signals display decoded itch values as soon they become available.  
These interfaces all follow the same format :

- `itch_<message_type>_early_v_o` : validity bit indicating a message of the `message_type` was detected.

- `itch_<message_type>_<field_name>_early_lite_v_o` : lite validity bit indicating the corresponding message field, 
    on the normal itch interface is complete. This validity should be evaluated alongside `itch_<message_type>_early_v_o`.

By default `EARLY` is defined.

## ITCH decoded message interface

The itch decoded message output's RTL is automatically generated.
More information is available in the [README.md](gen/README.md) of the `gen` folder.

These interfaces all follow the same format :

- `itch_<message_type>_v_o` : validity bit indicating a message of the `message_type` was decoded
    and the following fields are valid.

- `itch_<message_type>_<field_name>_o` : message field, fields are in big endian

## ( Optional ) GLIMPSE

To add the `End of Snapshot` message present only in the GLIMPSE extension the
`GLIMPSE` macro must be defined.

By default `GLIMPSE` should be defined.

## External modules

This code calls for some external modules that can be found : [https://github.com/Essenceia/rtl_utils](https://github.com/Essenceia/rtl_utils)
The makefile should point to this directory using `UTILS_DIR`.

## Test bench

Normal run :
```
make run
```

( Optional ) Debug mode activated, defines `DEBUG` and `DEBUG_ID`:
```
make run debug=1
```

Clean : 
```
make clean
```

## Formal

To run formal using yosys :

```
make formal
```

## License

This code is licensed under CC BY-NC 4.0, all rights belong to Julia Desmazes. 
