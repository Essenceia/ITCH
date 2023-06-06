ifndef debug
#debug := 
endif

FORMAL_DIR=formal
FORMAL_FILE=formal.sby

DEFINES=$(if $(debug),-DMOLD_MSG_IDS)

formal: tv_itch5.v
	sby -f ${FORMAL_DIR}/${FORMAL_FILE}
