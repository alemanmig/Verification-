#=========================================================
# Makefile — Simulación FSM (QuestaSim / Linux / Ubuntu)
# Autor: Miguel Alemán
#=========================================================

#-----------------------------------------
# Variables
#-----------------------------------------

# Herramientas del simulador (asegúrate de que estén en tu PATH)
VLIB = vlib
VLOG = vlog
VSIM = vsim

# Directorios
RTL_DIR   = ../rtl
TB_DIR    = ../tb
WORK_LIB  = work
TOP       = tb
WAVE_DO   = wave.do

# Archivos fuente
RTL_SRCS  = $(RTL_DIR)/fsm.sv
TB_SRCS   = $(TB_DIR)/fsm_property.sv $(TB_DIR)/tb.sv
UCDB_FILE = fsm.ucdb

#-----------------------------------------
# Targets principales
#-----------------------------------------

# Por defecto: compila y simula en modo consola
all: compile simulate

#-----------------------------------------
# Compilación
#-----------------------------------------
compile:
	@echo "========================================================="
	@echo "🔧 Compilando fuentes RTL y Testbench..."
	@echo "========================================================="
	@rm -rf $(WORK_LIB)
	@$(VLIB) $(WORK_LIB)
	@$(VLOG) -cover bcest $(RTL_SRCS)
	@$(VLOG) $(TB_SRCS)
	@echo "✅ Compilación completada correctamente."

#-----------------------------------------
# Simulación en modo consola
#-----------------------------------------
simulate:
	@echo "========================================================="
	@echo "🚀 Ejecutando simulación en modo consola..."
	@echo "========================================================="
	@$(VSIM) -c $(TOP) -do "run -all; coverage save $(UCDB_FILE); \
	vcover report $(UCDB_FILE); vcover report $(UCDB_FILE) -cvg -details; quit -f"
	@echo "✅ Simulación completada."

#-----------------------------------------
# Simulación en modo gráfico (GUI)
#-----------------------------------------
gui:
	@echo "========================================================="
	@echo "🖥️ Ejecutando simulación en modo gráfico (GUI)..."
	@echo "========================================================="
	@$(VSIM) -gui $(TOP) -do "do $(WAVE_DO); run -all; \
	coverage save $(UCDB_FILE); \
	vcover report $(UCDB_FILE); \
	vcover report $(UCDB_FILE) -cvg -details;"
	@echo "✅ Simulación completada en GUI."

#-----------------------------------------
# Limpieza de archivos temporales
#-----------------------------------------
clean:
	@echo "========================================================="
	@echo "🧹 Limpiando archivos temporales y resultados..."
	@echo "========================================================="
	@rm -rf $(WORK_LIB) $(UCDB_FILE) transcript vsim.wlf vsim.dbg
	@echo "✅ Limpieza completada."

#-----------------------------------------
# Ayuda
#-----------------------------------------
help:
	@echo "========================================================="
	@echo "📘 Opciones disponibles en el Makefile"
	@echo "========================================================="
	@echo "make all       → Compila y simula en modo consola"
	@echo "make compile   → Solo compila RTL y Testbench"
	@echo "make simulate  → Ejecuta simulación sin GUI"
	@echo "make gui       → Ejecuta simulación con GUI y wave.do"
	@echo "make clean     → Elimina archivos temporales"
	@echo "make help      → Muestra esta ayuda"
	@echo "========================================================="

