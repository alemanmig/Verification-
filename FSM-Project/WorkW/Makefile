#=========================================================
# Makefile — Simulación FSM (QuestaSim/ModelSim - Windows)
# Autor: Miguel Alemán — versión PowerShell compatible
#=========================================================

#-----------------------------------------
# Variables de ModelSim/QuestaSim
#-----------------------------------------
VSIM_HOME = D:/questasim64_2024.1
VLIB      = "$(VSIM_HOME)/win64/vlib.exe"
VLOG      = "$(VSIM_HOME)/win64/vlog.exe"
VSIM      = "$(VSIM_HOME)/win64/vsim.exe"

#-----------------------------------------
# Directorios y archivos
#-----------------------------------------
RTL_DIR   = ../rtl
TB_DIR    = ../tb
WORK_LIB  = WorkW
TOP       = tb
WAVE_DO   = wave.do
UCDB_FILE = fsm.ucdb

RTL_SRCS  = $(RTL_DIR)/fsm.sv
TB_SRCS   = $(TB_DIR)/fsm_property.sv $(TB_DIR)/tb.sv
UCDB_FILE = fsm.ucdb

#-----------------------------------------
# Targets principales
#-----------------------------------------
all: compile simulate

#-----------------------------------------
# Compilación con cobertura
#-----------------------------------------
compile:
	@echo =========================================================
	@echo  Compilando fuentes RTL y TB...
	@echo =========================================================
	@cmd /c "if exist $(WORK_LIB) rmdir /s /q $(WORK_LIB)"
	@$(VLIB) $(WORK_LIB)
	@$(VLOG) -cover bcest $(RTL_SRCS)
	@$(VLOG) +cover $(TB_SRCS)
	@echo Compilacion completada

#-----------------------------------------
# Simulación en modo consola (Solo reporte de texto)
#-----------------------------------------
simulate:
	@echo =========================================================
	@echo  Ejecutando simulacion en modo consola...
	@echo =========================================================
	@echo run -all > run_tmp.do
	@echo coverage save $(UCDB_FILE) >> run_tmp.do
	@echo vcover report $(UCDB_FILE) >> run_tmp.do
	@echo vcover report $(UCDB_FILE) -cvg -details >> run_tmp.do
	@echo quit -f >> run_tmp.do
	@cmd /c "$(VSIM) -c $(TOP) -do run_tmp.do"

#-----------------------------------------
# Simulación con GUI
#-----------------------------------------
gui:
	@echo =========================================================
	@echo Ejecutando simulación en modo grafico (GUI) con cobertura...
	@echo =========================================================
	@cmd /c "type $(WAVE_DO) | findstr /V /C:"wave clear" | findstr /V /C:"remove wave" > wave_tmp.do"
	@echo run -all >> wave_tmp.do
	@echo coverage save $(UCDB_FILE) >> wave_tmp.do
	@echo coverage open $(UCDB_FILE) >> wave_tmp.do
	@echo coverage report -details >> wave_tmp.do
#	#@echo coverage show -codeAll >> wave_tmp.do
#	#@echo coverage show -cvg >> wave_tmp.do
#	@echo coverage window -show >> wave_tmp.do
	@echo vcover report -html $(UCDB_FILE) >> wave_tmp.do
	@echo echo ========================================================= >> wave_tmp.do
	@echo echo  Simulación completada con cobertura habilitada >> wave_tmp.do
	@cmd /c "$(VSIM) -gui $(TOP) -do wave_tmp.do"


#-----------------------------------------
# Limpieza
#-----------------------------------------
clean:
	@echo =========================================================
	@echo 🧹 Limpiando archivos temporales y resultados...
	@echo =========================================================
	@cmd /c "if exist $(WORK_LIB) rmdir /s /q $(WORK_LIB)"
	@cmd /c "if exist $(UCDB_FILE) del /q $(UCDB_FILE)"
	@cmd /c "if exist transcript del /q transcript"
	@cmd /c "if exist vsim.wlf del /q vsim.wlf"
	@cmd /c "if exist vsim.dbg del /q vsim.dbg"
	@cmd /c "if exist run_tmp.do del /q run_tmp.do"
	@cmd /c "if exist wave_tmp.do del /q wave_tmp.do"
	@echo ✅ Limpieza completada

#-----------------------------------------
# Ayuda
#-----------------------------------------
help:
	@echo =========================================================
	@echo 📘 Opciones disponibles en el Makefile
	@echo =========================================================
	@echo make all       → Compila y simula en modo consola
	@echo make compile   → Solo compila RTL y Testbench
	@echo make simulate  → Ejecuta simulación sin GUI (solo texto)
	@echo make gui       → Ejecuta simulación con GUI y cobertura visual
	@echo make clean     → Elimina archivos temporales
	@echo make help      → Muestra esta ayuda
	@echo =========================================================
