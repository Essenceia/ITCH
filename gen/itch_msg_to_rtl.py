import xmltodict
import pprint
import sys
import math

# conf list
PORT_LIST_FILE = "port_list.v"
ASSIGN_LOGIC_FILE = "assign_logic.v"

MOLD_MSG_CNT_SIG="data_cnt_q"
MOLD_MSG_LEN=8
MOLD_MSG_DATA_SIG="data_q"

ITCH_MSG_TYPE_SIG="itch_msg_type"

SIG_PREFIX="itch_"

def parse_valid(msg_name, msg_type, msg_len, port_f, assign_f):
    sig_name = SIG_PREFIX + msg_name + "_v_o"
    # get the ascii code for the message type
    msg_type_i = ord(msg_type)
    exp_msg_cnt = math.ceil(int(msg_len)/MOLD_MSG_LEN)
    sig_logic = "("+ITCH_MSG_TYPE_SIG + " == 'd"+str(msg_type_i)+") & ("+MOLD_MSG_CNT_SIG+" == 'd"+str(exp_msg_cnt)+")"

    port_f.write("\noutput logic "+sig_name+",\n")
    assign_f.write("\nassign "+sig_name+" = "+sig_logic+";\n")

def parse_field(msg_name, field, port_f, assign_f):
    f_name = field['@name']
    f_len  = field['@len']
    f_offset = field['@offset']
    if not( f_name == "message_type" ):
        sig_name = SIG_PREFIX+msg_name+"_"+f_name+"_o"
        sig_dim = "["+f_len+"*LEN-1:0]"
        sig_logic = MOLD_MSG_DATA_SIG+"[LEN*"+f_offset+"+LEN*"+f_len+"-1:LEN*"+f_offset+"]"

        port_f.write("output logic "+sig_dim+" "+sig_name+",\n")
        assign_f.write("assign "+sig_name+" = "+sig_logic+";\n") 

# Parse args.
assert(len(sys.argv) == 2);
path = sys.argv[1]
assert(type(path) is str)

# Open XML file.
with open(path, 'r', encoding='utf-8') as file:
    my_xml = file.read()

# Open or create output files
port_f = open("port_list.v","w")
assign_f = open("assign_logic.v","w")

# Parse XML
content = xmltodict.parse(my_xml)

# Read Strucsts
structs = content['Model']['Structs']['Struct']
for struct in structs:
    msg_name=struct['@name']
    msg_type=struct['@id']
    msg_len=struct['@len']
    parse_valid(msg_name , msg_type, msg_len, port_f, assign_f )
    
    for field in struct['Field']:
        #print(type(field))
        if type(field) is dict:
            parse_field(msg_name, field, port_f, assign_f)
        else:
            assert(0)
print("Generated RTL stored in :\nport list : "+PORT_LIST_FILE+"\nassignement logic : "+ASSIGN_LOGIC_FILE)
