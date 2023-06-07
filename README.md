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

### MoldUPD64 session id and sequence number

To add internal flopping of the session id and sequence number information the
`MOLD_MSG_IDS` macro need's to be defined.

By default `MOLD_MSG_IDS` should be defined.

## Test bench

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
