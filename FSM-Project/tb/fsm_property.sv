//======================
// Properties FSM
// Module fsm_property
//======================

module fsm_property(pclk,prst,pdin,pdout);
  input pclk,prst,pdin,pdout;
  
  // Assertions

  // 1. Tras reset, el estado debe ser 'idle'
  property p_reset_idle;
    @(posedge pclk) prst |-> dut.state == dut.idle;
  endproperty
  assert property(p_reset_idle)
    else $error("FSM no entra en 'idle' tras reset");

  // 2. Transición de idle a s0 cuando rst == 0
  property p_idle_to_s0;
    @(posedge pclk) dut.state == dut.idle && !prst |-> dut.next_state == dut.s0;
  endproperty
  assert property(p_idle_to_s0)
    else $error("FSM no transita de 'idle' a 's0' correctamente");

  // 3. En estado s1 con din == 1, dout debe ser 1
  property p_s1_din1_dout1;
    @(posedge pclk) dut.state == dut.s1 && pdin == 1 |-> pdout == 1;
  endproperty
  assert property(p_s1_din1_dout1)
    else $error("FSM no genera 'dout == 1' en estado 's1' con 'din == 1'");

  // 4. En cualquier otro caso, dout debe ser 0
  property p_dout_zero_else;
    @(posedge pclk) !(dut.state == dut.s1 && pdin == 1) |-> pdout == 0;
  endproperty
  assert property(p_dout_zero_else)
    else $error("FSM genera 'dout == 1' fuera de condición válida");

  // 5. Transición de s0 a s1 si din == 1
  property p_s0_to_s1;
    @(posedge pclk) dut.state == dut.s0 && pdin == 1 |-> dut.next_state == dut.s1;
  endproperty
  assert property(p_s0_to_s1)
    else $error("FSM no transita de 's0' a 's1' con 'din == 1'");
    
  endmodule