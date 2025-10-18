# JasperGold Formal Verification Script
# FSM assertions check
clear -all

analyze -sv ../rtl/fsm.sv
analyze -sv ../tb/fsm_property.sv +define+FORMAL

elaborate -top fsm

clock clk
reset -expression rst