#=========================================================
# wave.do — configuración de señales de onda para FSM
# Autor: Miguel Alemán
#=========================================================

# Limpiar la ventana de ondas anterior
quietly wave clear
quietly remove wave *

# Configurar la vista
view wave
view structure
view signals
view variables

# Añadir señales principales del testbench
add wave -divider {Testbench Signals}
add wave -noupdate -color white sim:/tb/clk
add wave -noupdate -color white sim:/tb/rst
add wave -noupdate -color yellow sim:/tb/din
add wave -noupdate -color cyan sim:/tb/dout

# Añadir señales internas del DUT (fsm)
add wave -divider {FSM Internals}
add wave -noupdate -color green sim:/tb/dut/state
add wave -noupdate -color orange sim:/tb/dut/next_state

# Si quieres observar los estados por nombre en lugar de binario:
radix define state_enum {
    1 {idle}
    2 {s0}
    4 {s1}
}
radix set -decimal sim:/tb/dut/state
radix set -decimal sim:/tb/dut/next_state

# Añadir señales de assertions (opcional, si deseas verlas)
add wave -divider {Assertions / Properties}
add wave -noupdate -color magenta sim:/tb/fsm_bind_inst/*

# Configuración de la escala de tiempo
configure wave -timelineunits ns
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -griddelta 5
configure wave -gridoffset 0
configure wave -gridsnap 0

# Autozoom y actualización
update
wave zoom full
