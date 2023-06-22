# RTL generation

As the RTL code for the itch decoder is simple but repetitive.
We generate it using and `xml` file outlining the itch message format and a small script 
`itch_msg_to_rtl.py`.

## Usage :

To run script :
```
python itch_msg_to_rtl.py nasdaq_totalview_itch.xml
```

Note : `python` is assumed to be `python3`, tested with python version :
`Python 3.11.3 (main, Apr  5 2023, 15:52:25) [GCC 12.2.1 20230201] on linux`.

## Generated files

This program generates 5 files, these files will be produced in the directory where
the script is run.

- `port_list.v` top level itch interface ports.

- `assign_logic.v` assign logic for driving decoder.

- `formal.v` formal assertions.

- `tb_port_list.v` port list for using the itch module in the test bench.

- `tb_sig_list.v` declaration of the signals to be connected to itch module for use in the test bench.


## Generation configuration

Generation results can be altered by modifying the following situated at the top of the script :

- `SIG_PREFIX` signal name prefix, default `itch_`

- `SVA_PREFIX` system verilog formal assertion name prefix, default `sva_`
 
- `PORT_LIST_FILE` output file name for the generated port list, default `port_list.v`

- `ASSIGN_LOGIC_FILE` output file name for the assignation logic, default `assign_logic.v`

- `FORMAL_FILE` output file name for the formal assertions, default `formal.v`

- `TB_PORT_LIST_FILE` output file name for the itch module's ports, used when 
    creating an instance of the itch module it the test bench, default `tb_port_list.v`

- `TB_SIG_LIST_FILE` output file name for the declarations of the signals connected to an instance
    of our itch module when used in the test bench, default `tb_sig_list.v` 

- `MOLD_MSG_CNT_SIG` name for the net that stores the count of mold message payloads we have already received, default `data_cnt_q`

- `MOLD_MSG_LEN` number of bytes each payload contains, default `8`

- `MOLD_MSG_DATA_SIG` name of the net on which the payload data is stored, default `data_q`

- `ITCH_MSG_TYPE_SIG` name of the net on which the itch message type data is stored, default `itch_msg_type` 

## ITCH message `xml` file

Originally found in https://github.com/doctorbigtime/itch, all credits belong to `doctorbigtime`.

Was modified to remove all none itch messages under `Structs`, diffs can be viewed in `xml_diff.patch`.
