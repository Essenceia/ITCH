ifndef debug
#debug := 
endif

FORMAL_DIR=formal
FORMAL_FILE=formal.sby
TB_DIR=tb

BUILD=build
CONF=conf

FLAGS=-Wall -g2012 -gassertions -gstrict-expr-width
DEFINES=$(if $(debug),-DMOLD_MSG_IDS)

WAVE_FILE=wave.vcd
WAVE_CONF=wave.conf

VIEW=gtkwave

all: run

formal: tv_itch5.v
	sby -f ${FORMAL_DIR}/${FORMAL_FILE}

formal_wave: 
	${VIEW} ${FORMAL_DIR}/formal_basic/engine_0/trace.vcd ${WAVE_CONF}

test: ${TB_DIR}/tv_itch5_tb.v tv_itch5.v
	iverilog ${FLAGS} -s tv_itch5_tb ${DEFINES} -o ${BUILD}/tb tv_itch5.v ${TB_DIR}/tv_itch5_tb.v

run: test
	vvp ${BUILD}/tb

wave: run
	${VIEW} ${BUILD}/${WAVE_FILE} ${BUILD}/${WAVE_CONF}
	
clean:
	rm -fr ${BUILD}/*
	rm -fr ${FORMAL_DIR}/{formal_basic,formal_cover}	
