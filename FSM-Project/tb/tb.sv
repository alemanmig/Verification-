`timescale 1ns/1ps

//`include "fsm_property.sv"

//=================
// Testbenche FSM
// Modulo tb_top
//==================


module tb;

  // Señales del DUT
  logic clk;
  logic rst;
  logic din;
  logic dout;

  // Instancia del DUT
  fsm dut (
    .clk(clk),
    .rst(rst),
    .din(din),
    .dout(dout)
  );
  
  // Properties bind
  
  bind fsm fsm_property fsm_bind_inst (.pclk(clk),
                                       .prst(rst),
                                       .pdin(din),
                                       .pdout(dout)
                                      );

  // Generación de reloj
  initial clk = 0;
  always #5 clk = ~clk; // 100 MHz

  // Tareas auxiliares
  task reset_dut();
    rst = 1;
    din = 0;
    @(posedge clk);
    rst = 0;
    @(posedge clk);
  endtask

  task apply_input(logic in);
    din = in;
    @(posedge clk);
  endtask

  // Estímulo principal
  initial begin
    $display("Inicio de simulación");
    reset_dut();

    // Secuencia de prueba
    apply_input(0); // idle → s0
    apply_input(1); // s0 → s1
    apply_input(1); // s1 → s0, dout debe ser 1
    apply_input(0); // s0 → s0
    apply_input(1); // s0 → s1
    apply_input(0); // s1 → s1
    apply_input(1); // s1 → s0, dout debe ser 1

    // Fin de simulación
    #20;
    $finish;
  end

  // Monitor simple
  always @(posedge clk) begin
    $display("Time=%0t | rst=%b din=%b dout=%b", $time, rst, din, dout);
  end
  
  // Assertions
  
    // Clocking block para sincronización
  clocking cb @(posedge clk);
    input rst, din, dout;
  endclocking

  
  // Covergroup para cobertura funcional
    
  covergroup cg_fsm @(posedge clk);
    // Cobertura de estados
    coverpoint dut.state {
      bins idle = {dut.idle};
      bins s0   = {dut.s0};
      bins s1   = {dut.s1};
    }

    // Cobertura de entradas
    coverpoint din {
      bins zero = {0};
      bins one  = {1};
    }

    // Transiciones de estado
    coverpoint dut.next_state {
      bins to_idle = {dut.idle};
      bins to_s0   = {dut.s0};
      bins to_s1   = {dut.s1};
    }

    // Cruce de estado actual y entrada
    cross dut.state, din;

    // Cruce de estado actual y próximo estado
    cross dut.state, dut.next_state;

    // Cobertura de salida
    coverpoint dout {
      bins dout_0 = {0};
      bins dout_1 = {1};
    }

    // Cruce de estado y salida
  cross dut.state, dout;
  endgroup

  // Instancia del covergroup
  cg_fsm fsm_cov = new();
    
  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    $assertvacuousoff(0); 
  end

endmodule