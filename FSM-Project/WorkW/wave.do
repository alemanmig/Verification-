onerror {resume}
radix define state_enum {
    "1" "idle",
    "2" "s0",
    "4" "s1",
    -default default
}
quietly WaveActivateNextPane {} 0
add wave -noupdate -divider {Testbench Signals}
add wave -noupdate -color white /tb/dut/clk
add wave -noupdate -color white /tb/dut/rst
add wave -noupdate -color yellow /tb/dut/din
add wave -noupdate -color cyan /tb/dut/dout
add wave -noupdate -divider {FSM Internals}
add wave -noupdate -color green /tb/dut/state
add wave -noupdate -color orange /tb/dut/next_state
TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 ps} 0}
quietly wave cursor active 0
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits ps
update
WaveRestoreZoom {0 ps} {1024 ns}
