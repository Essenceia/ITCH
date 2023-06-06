# ITCH decoder

RTL implementation of a Nasdaq TotalView-ITCH 5.0 decoder.

Designed to work alongside the MoldUPD64 module https://github.com/Essenceia/MoldUPD64.

## GLIMPSE

To add the `End of Snapshot` message present only in the GLIMPSE extention the
`GLIMPSE` macro must be defined.

This can be done by adding it to the list of `DEFINES` in the `Makefile`.

```
DEFINE=-DGLIMPSE <other defines>
```

By default `GLIMPSE` should be defined.

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
