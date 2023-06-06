# Generator

As the RTL code for the itch decoder is simple but repetitive it is generated 
using and xml file outlining the itch message format anf the python script 
`itch_msg_to_rtl.py`.

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

`MOLD_MSG_CNT_SIG` name for the net that stores the count of mold message payloads we have already received, default `data_cnt_q`

`MOLD_MSG_LEN` number of bytes each payload contains, default `8`

`MOLD_MSG_DATA_SIG` name of the net on which the payload data is stored, default `data_q`

`ITCH_MSG_TYPE_SIG` name of the net on which the itch message type data is stored, default `itch_msg_type` 

## ITCH message xml file

Originally found in https://github.com/doctorbigtime/itch, all credits belong to `doctorbigtime`.

Was modified to remove all none itch messages under `Structs`, diffs can be viewed in `xml_diff.patch`.
