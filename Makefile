ifndef debug
#debug := 
endif

FORMAL_DIR=formal
FORMAL_FILE=formal.sby
VIEW=gtkwave
WAVE_CONF=wave.conf

DEFINES=$(if $(debug),-DMOLD_MSG_IDS)

formal: tv_itch5.v
	sby -f ${FORMAL_DIR}/${FORMAL_FILE}

formal_wave: 
	${VIEW} ${FORMAL_DIR}/formal_basic/engine_0/trace.vcd ${WAVE_CONF}
