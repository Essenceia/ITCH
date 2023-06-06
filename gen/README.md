# Generator

As the RTL code for the itch decoder is simple but repetitive.
We generate it using and xml file outlining the itch message format and a small script 
`itch_msg_to_rtl.py`.

This will generate 3 files :

`port_list.v` output port list

`assign_logic.v` assignation logic to identify the itch message corresponding to the flopped mold message
    and correctly break down all it's filed to drive the module outputs

`formal.v` system verilog formal assertions to verify behavior of module and perform sanity checks on outputs

Usage :
```
python itch_msg_to_rtl.py nasdaq_totalview_itch.xml
```

Generation results can be altered by modifying the following situated at the top of the script :

`SIG_PREFIX` signal name prefix, default `itch_`

`SVA_PREFIX` system verilog formal assertion name prefix, default `sva_`
 
`PORT_LIST_FILE` output file name for the generated port list, default `port_list.v`

`ASSIGN_LOGIC_FILE` output file name for the assignation logic, default `assign_logic.v`

`FORMAL_FILE` output file name for the formal assertions, default `formal.v`

`TB_PORT_LIST_FILE` output file name for the itch module's ports, used when 
    creating an instance of the itch module it the test bench, default `tb_port_list.v`

`TB_SIG_LIST_FILE` output file name for the declarations of the signals connected to an instance
    of our itch module when used in the test bench, default `tb_sig_list.v` 

`MOLD_MSG_CNT_SIG` name for the net that stores the count of mold message payloads we have already received, default `data_cnt_q`

`MOLD_MSG_LEN` number of bytes each payload contains, default `8`

`MOLD_MSG_DATA_SIG` name of the net on which the payload data is stored, default `data_q`

`ITCH_MSG_TYPE_SIG` name of the net on which the itch message type data is stored, default `itch_msg_type` 

## ITCH message xml file

Originally found in https://github.com/doctorbigtime/itch, all credits belong to `doctorbigtime`.

Was modified to remove all none itch messages under `Structs`, diffs can be viewed in `xml_diff.patch`.
