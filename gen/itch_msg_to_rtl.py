import xmltodict
import pprint
import sys
import math

# conf list
PORT_FILE = "port_list.v"
EARLY_PORT_FILE = "early_port_list.v"
IF_ITCH_FILE = "if_itch.v"
ASSIGN_LOGIC_FILE = "assign_logic.v"
ASSIGN_EARLY_LOGIC_FILE = "assign_early_logic.v"
IF_EARLY_FILE = "if_early.v"
FORMAL_FILE = "formal.v"
TB_PORT_LIST_FILE = "tb_port_list.v"
TB_SIG_LIST_FILE = "tb_sig_list.v"

MOLD_MSG_CNT_SIG="data_cnt_q"
MOLD_MSG_LEN=8
MOLD_MSG_DATA_SIG="data_q"

ITCH_MSG_TYPE_SIG="itch_msg_type"

SIG_PREFIX="itch_"
SVA_PREFIX="sva_"

def parse_valid(msg_name, msg_type, msg_len, if_itch_f, assign_f, tb_port_f, tb_sig_f, if_early_f, early_assign_f,port_f, early_port_f ):
    sig_name =SIG_PREFIX+ msg_name + "_v_o"
    lite_sig_name = msg_name + "_lite_v"
    early_sig_name =  SIG_PREFIX + msg_name + "_early_v_o"
    # get the ascii code for the message type
    lite_sig_logic = "("+ITCH_MSG_TYPE_SIG + " == \""+msg_type+"\")"
    early_sig_logic = lite_sig_name +" & ("+MOLD_MSG_CNT_SIG+" == 'd1)" 
    sig_logic = lite_sig_name+" & ("+MOLD_MSG_CNT_SIG+" == 'd"+msg_len+")"

    if_itch_f.write("\nlogic "+sig_name+";\n")
    port_f.write("\noutput logic "+sig_name+",\n")
    early_port_f.write("\noutput logic "+early_sig_name+",\n")
    assign_f.write("\nlogic "+lite_sig_name+";\n"
    +"assign "+lite_sig_name+" = "+lite_sig_logic+";\n"
    +"assign "+sig_name+" = "+sig_logic+";\n")
    tb_port_f.write("\n."+sig_name+"("+sig_name+"),\n") 
    tb_sig_f.write("\nlogic "+sig_name+";\n")

    # early
    if_early_f.write("\nlogic "+early_sig_name+";\n")
    early_assign_f.write("\nassign "+early_sig_name+" = "+early_sig_logic+";\n")
    return sig_name

def parse_field(msg_name, field, if_itch_f, assign_f, tb_port_f, tb_sig_f, if_early_f, early_assign_f, port_f, early_port_f):
    f_name = field['@name']
    f_len  = field['@len']
    f_offset = field['@offset']
    sig_name =""
    if not( f_name == "message_type" ):
        sig_name =SIG_PREFIX+ msg_name+"_"+f_name+"_o"
        sig_dim = "["+f_len+"*LEN-1:0]"
        sig_logic = MOLD_MSG_DATA_SIG+"[LEN*"+f_offset+"+LEN*"+f_len+"-1:LEN*"+f_offset+"]"

        port_f.write("output logic "+sig_dim+" "+sig_name+",\n")
        if_itch_f.write("logic "+sig_dim+" "+sig_name+";\n")
        assign_f.write("assign "+sig_name+" = "+sig_logic+";\n") 
        tb_port_f.write("."+sig_name+"("+sig_name+"),\n")
        tb_sig_f.write("logic "+sig_dim+" "+sig_name+";\n")

        # early valid for the data
        early_sig_name =  SIG_PREFIX + msg_name+"_"+f_name+"_early_lite_v_o"
        if_early_f.write("logic "+early_sig_name+";\n")
        early_port_f.write("output logic "+early_sig_name+",\n")
        early_sig_logic = MOLD_MSG_CNT_SIG+" >= 'd"+str(int(f_offset)+int(f_len))
        early_assign_f.write("assign "+early_sig_name+" = "+early_sig_logic+";\n") 
    return sig_name

def formal_onehot0_valid(sig_arr, formal_f):
    sva_arr = "{"
    for i in range(len(sig_arr)):
        if not ( i == 0 ):
            sva_arr += ","
        sva_arr += sig_arr[i]
    sva_arr += "}"
    sva_name = SVA_PREFIX + "itch_msg_valid_onehot0"
    sva_logic = sva_name +" : assert( $onehot0("+sva_arr+"))"
    formal_f.write(sva_logic+";\n")

def formal_fields_xcheck(sig_valid, sig_arr, formal_f):
    sva_arr = "("
    for i in range(len(sig_arr)):
        if not ( i == 0 ) :
            sva_arr += " | "
        sva_arr+= "|"+sig_arr[i]
    sva_arr += ")"
    sva_name = SVA_PREFIX+"xcheck_"+sig_valid[:-3]+"data"
    sva_logic = sva_name +" : assert( ~"+sig_valid+" | ("+sig_valid+" & ~$isunknown("+sva_arr+")))"
    formal_f.write(sva_logic+";\n\n")

def formal_valid_xcheck(sig_valid, formal_f):
    sva_name = SVA_PREFIX +"xcheck_"+ sig_valid 
    sva_logic = sva_name + " : assert( ~$isunknown("+sig_valid+"))"
    formal_f.write(sva_logic+";\n")

def main():
    # Parse args.
    assert(len(sys.argv) == 2);
    path = sys.argv[1]
    assert(type(path) is str)
    
    # Open XML file.
    with open(path, 'r', encoding='utf-8') as file:
        my_xml = file.read()
    
    # Open or create output files
    port_f = open(PORT_FILE,"w")
    early_port_f = open(EARLY_PORT_FILE,"w")
    if_itch_f = open(IF_ITCH_FILE,"w")
    assign_f = open(ASSIGN_LOGIC_FILE,"w")
    early_assign_f = open(ASSIGN_EARLY_LOGIC_FILE,"w")
    if_early_f = open(IF_EARLY_FILE,"w")
    formal_f = open(FORMAL_FILE,"w")
    tb_port_f = open(TB_PORT_LIST_FILE,"w")
    tb_sig_f = open(TB_SIG_LIST_FILE,"w")
    
    # Parse XML
    content = xmltodict.parse(my_xml)
    
    # declare empty list
    sig_v_arr = []
    sig_field_arr = []
    
    # Read Strucsts
    structs = content['Model']['Structs']['Struct']
    for struct in structs:
        msg_name=struct['@name']
        msg_type=struct['@id']
        msg_len=struct['@len']
        sig_v = parse_valid(msg_name , msg_type, msg_len, if_itch_f, assign_f, tb_port_f, tb_sig_f, if_early_f , early_assign_f, port_f, early_port_f)
        formal_valid_xcheck(sig_v, formal_f)
        sig_v_arr.append(sig_v)
        # clear list
        sig_field_arr.clear()
        for field in struct['Field']:
            #print(type(field))
            if type(field) is dict:
                sig_field = parse_field(msg_name, field, if_itch_f, assign_f, tb_port_f, tb_sig_f,if_early_f , early_assign_f, port_f, early_port_f)
                if len(sig_field) > 0:
                    sig_field_arr.append(sig_field)
            else:
                assert(0)
        formal_fields_xcheck(sig_v, sig_field_arr , formal_f)
    formal_onehot0_valid(sig_v_arr, formal_f)
    print("RTL generated")

main()
