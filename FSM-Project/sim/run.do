if [file exists "work"] {vdel -all}
vlib work

#Compile RTL
vlog -cover bcest ../rtl/fsm.sv

#Compile TB
vlog ../tb/fsm_property.sv
vlog ../tb/tb.sv

vsim tb -coverage -do "wave.do"
set NoQuitOnFinish 1
onbreak {resume}
log /* -r
run -all

coverage save fsm.ucdb
vcover report fsm.ucdb
vcover report fsm.ucdb -cvg -details
quit 
