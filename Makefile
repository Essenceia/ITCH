ifndef debug
#debug := 
endif

FORMAL_DIR=formal
FORMAL_FILE=formal.sby
TB_DIR=tb
UTILS_DIR=../utils

BUILD=build
CONF=conf

FLAGS=-Wall -g2012 -gassertions -gstrict-expr-width
DEFINES=-DGLIMPSE -DEARLY $(if $(debug),-DDEBUG -DDEBUG_ID) 

WAVE_FILE=wave.vcd
WAVE_CONF=wave.conf

VIEW=gtkwave

all: run

formal: tv_itch5.v
	sby -f ${FORMAL_DIR}/${FORMAL_FILE}

formal_wave: 
	${VIEW} ${FORMAL_DIR}/formal_basic/engine_0/trace.vcd ${WAVE_CONF}

dec: tv_itch5_dec.v
	iverilog ${FLAGS} -s tv_itch5_dec ${DEFINES} -o ${BUILD}/tv_itch5_dec ${UTILS_DIR}/len_to_mask.v tv_itch5_dec.v

mux: tv_itch5_mux.v
	iverilog ${FLAGS} -s tv_itch5_mux ${DEFINES} -o ${BUILD}/tv_itch5_mux tv_itch5_mux.v

tv_itch5: dec tv_itch5.v mux
	iverilog ${FLAGS} -s tv_itch5 ${DEFINES} -o ${BUILD}/tv_itch5 ${UTILS_DIR}/len_to_mask.v tv_itch5_dec.v tv_itch5_mux.v tv_itch5.v

test: ${TB_DIR}/tv_itch5_tb.v tv_itch5.v mux dec
	iverilog ${FLAGS} -s tv_itch5_tb ${DEFINES} -o ${BUILD}/tb tv_itch5.v ${UTILS_DIR}/len_to_mask.v tv_itch5_dec.v tv_itch5_mux.v ${TB_DIR}/tv_itch5_tb.v

run: test
	vvp ${BUILD}/tb

wave: run
	${VIEW} ${BUILD}/${WAVE_FILE} ${BUILD}/${WAVE_CONF}
	
clean:
	rm -fr ${BUILD}/*
	rm -fr ${FORMAL_DIR}/{formal_basic,formal_cover}	
