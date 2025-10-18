################################################################################
# Makefile para Cadence Xcelium / JasperGold
# Proyecto: FSM + Testbench con Assertions y Cobertura
# Autor: Miguel Alemán
################################################################################

# Carpetas base
RTL_DIR      := ../rtl
TB_DIR       := ../tb
WORK_DIR     := .
LOG_DIR      := $(WORK_DIR)/logs
COV_DIR      := $(WORK_DIR)/coverage
FORMAL_DIR   := $(WORK_DIR)/formal

# Archivos fuente
SRCS         := $(RTL_DIR)/fsm.sv \
                $(TB_DIR)/tb.sv \
                $(TB_DIR)/fsm_property.sv

# Nombre de simulación / ejecutables
TOP          := tb
SIM_LOG      := $(LOG_DIR)/sim.log
COMP_LOG     := $(LOG_DIR)/comp.log

# Configuración general de simulación
TIMESCALE    := 1ns/1ps
ACCESS       := +rwc
DEFINES      := +define+XCELIUM
XRUN_OPTS    := -64bit -sv -timescale $(TIMESCALE) -access $(ACCESS) $(DEFINES)

# Configuración cobertura
COV_OPTS     := -coverage all -covoverwrite
COV_GUI_DB   := cov_work/scope/merged

# JasperGold TCL para formal
FORMAL_TCL   := $(FORMAL_DIR)/fsm_formal.tcl

################################################################################
# Targets principales
################################################################################

help:
	@echo ""
	@echo "📘  Targets disponibles:"
	@echo "   make sim           -> Compila y corre la simulación (sin GUI)"
	@echo "   make sim_gui       -> Compila y corre con SimVision"
	@echo "   make cov           -> Simulación con cobertura habilitada"
	@echo "   make cov_gui       -> Abre IMC para visualizar cobertura"
	@echo "   make formal        -> Ejecuta JasperGold (modo batch)"
	@echo "   make formal_gui    -> Ejecuta JasperGold (modo GUI)"
	@echo "   make clean         -> Limpia archivos generados"
	@echo ""

################################################################################
# Simulación
################################################################################

sim:
	@mkdir -p $(LOG_DIR)
	xrun $(XRUN_OPTS) $(SRCS) -top $(TOP) -l $(SIM_LOG)

sim_gui:
	@mkdir -p $(LOG_DIR)
	xrun $(XRUN_OPTS) $(SRCS) -top $(TOP) -l $(SIM_LOG) -gui

################################################################################
# Simulación con cobertura
################################################################################

cov:
	@mkdir -p $(LOG_DIR) $(COV_DIR)
	xrun $(XRUN_OPTS) $(COV_OPTS) $(SRCS) -top $(TOP) -l $(LOG_DIR)/cov.log

cov_gui:
	imc -load $(COV_GUI_DB)

################################################################################
# Formal con JasperGold
################################################################################

formal:
	@mkdir -p $(FORMAL_DIR)
	jaspergold -allow_unsupported_OS $(FORMAL_TCL) -no_gui

formal_gui:
	@mkdir -p $(FORMAL_DIR)
	jaspergold -allow_unsupported_OS $(FORMAL_TCL)

################################################################################
# Limpieza
################################################################################

clean:
	rm -rf xrun* xcelium* *.log logs/ cov_work/ shm_db/ .sim* .svm* cov* imc* mdv* \
	       waves* *.shm *.err *.key worklib/ INCA_libs/ *.history \
	       formal/coverage* $(FORMAL_DIR) $(COV_DIR)
	@echo "🧹 Limpieza completa."

################################################################################
# Fin del Makefile
################################################################################
