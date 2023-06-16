# ITCH decoder

RTL implementation of a Nasdaq TotalView-ITCH 5.0 decoder.

Designed to work alongside the MoldUPD64 module https://github.com/Essenceia/MoldUPD64.

## Optional features

The module includes a few optional features that can be included or not depending
on the defined macro's. These macro's are defined in the `Makefile`.

### GLIMPSE

To add the `End of Snapshot` message present only in the GLIMPSE extension the
`GLIMPSE` macro must be defined.

By default `GLIMPSE` should be defined.

### DEBUG id

To help debuging, whenever the `DEBUG_ID` flag is set an new identification
number will be attacked to each message. This id is driven by the `debug_id_i`
input and is outputed alongside the decoded message on `debug_id_o`.

This is used to keep track of individual itch messages in the top level
testbench.

By default `DEBUG_ID` should be not defined.

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

## RTL generation

A major part of this RTL is automatically generated, for more information 
see the `README.md` in the `gen` folder.

## License

This code is licensed under CC BY-NC 4.0, to obtain a commercial license
reach out to the author . 
