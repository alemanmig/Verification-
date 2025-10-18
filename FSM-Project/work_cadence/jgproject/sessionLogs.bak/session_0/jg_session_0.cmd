# ----------------------------------------
# Jasper Version Info
# tool      : Jasper 2024.09
# platform  : Linux 4.18.0-348.7.1.el8_5.x86_64
# version   : 2024.09 FCS 64 bits
# build date: 2024.09.26 14:35:17 UTC
# ----------------------------------------
# started   : 2025-10-17 22:33:10 CDT
# hostname  : pc-064-244.cic.ipn.mx.(none)
# pid       : 384764
# arguments : '-label' 'session_0' '-console' '//127.0.0.1:37857' '-style' 'windows' '-data' 'AAAAxHicY2RgYLCp////PwMYMD6A0Aw2jAyoAMRnQhUJbEChGRhYYZphSkAatBh0GRIZcoAwn6GcIZ6hlCGPoRhIFgBhPkMRQwlDKkMKUNyfIRioWg8I9RnSwDK5YH0gXjGQHY8iqgfUlwykQQAABpAYMw==' '-proj' '/home/maleman/MyLib45/git_alemanmig/Verification-/FSM-Project/work_cadence/jgproject/sessionLogs/session_0' '-init' '-hidden' '/home/maleman/MyLib45/git_alemanmig/Verification-/FSM-Project/work_cadence/jgproject/.tmp/.initCmds.tcl' './formal/fsm_formal.tcl'
# JasperGold Formal Verification Script
# FSM assertions check
clear -all

analyze -sv ../rtl/fsm.sv
analyze -sv ../tb/fsm_property.sv +define+FORMAL

elaborate -top fsm

clock clk
reset -expression rst
prove -bg -all
