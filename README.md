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
	parameter AXI_DATA_W = 64,
	parameter AXI_KEEP_W = AXI_DATA_W / 8,
	
	// itch data
	parameter LEN = 8,

	// maximum length an itch message ( net order imbalance )
	parameter MSG_MAX_W = 50*LEN, 

	// maximum number of payloads that need to be received for the longest itch message 
	// $ceil(MSG_MAX_W / AXI_DATA_W) 
	parameter CNT_MAX = 7,
	parameter CNT_MAX_W = $clog2(CNT_MAX)
)(
	input clk,
	input nreset,

	//message
	input valid_i,
	input start_i,
	input [AXI_DATA_W-1:0] data_i,

	`ifdef DEBUG_ID
	// debug id associated with current message, used to track
	// messages through pipeline for debug
	input  [DEBUG_ID_W-1:0] debug_id_i,
	output [DEBUG_ID_W-1:0] debug_id_o,
	`endif 


    [ITCH decoded messages iterface]
```

### Mold message

Mold message data driven by moldudp64 module, Since itch messages are of 
fixed length depending on the itch message type we are not including a mask
field to indicate each validity of the `data_i` bytes.

- `valid_i` : validity bit, mold message is currently getting transferred.

- `start_i` : start of a new mold message.

- `data_i` : mold message data, 8 byte aligned.

### ( Optional ) Debug id

To help debugging, whenever the `DEBUG_ID` flag is set an new identification
number will be attacked to each message.

This is used to keep track of individual itch messages in the top level
test bench.

By default `DEBUG_ID` should be not defined.

- `debug_id_i` : debug id tracking each new mold message, valid when `start_i` and 
    `valid_i` are set.

- `debug_id_o` : debug id of the decoded itch message, valid when any `itch_<message_type>_v_o`
    validity bit is set.

## ITCH decoded message interface

The itch decoded message output's RTL is automatically generated.
More information is available in the [README.md](gen/README.md) of the `gen` folder.

These interfaces all follow the same format :

- `itch_<message_type>_v_o` : validity bit indicating a message of the `message_type` was decoded
    and the following fields are valid.

- `itch_<message_type>_<field_name>_o` : message field, fields are in big endian

### ( Optional ) GLIMPSE

To add the `End of Snapshot` message present only in the GLIMPSE extension the
`GLIMPSE` macro must be defined.

By default `GLIMPSE` should be defined.

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
