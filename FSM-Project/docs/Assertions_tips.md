- [Assertions en SystmeVerilog](#assertions-en-systmeverilog)
  - [Properties en un diseño](#properties-en-un-diseño)
  - [¿Assertions?](#assertions)


# Assertions en SystmeVerilog

> Esta guía resume el uso de assertions para validar propiedades funcionales y temporales en diseños digitales. Incluye ejemplos, buenas prácticas y comparaciones con checkers tradicionales.
>
> ## ¿Qué es una assertion?

Una *assertion* es una afirmación que debe mantenerse verdadera durante la simulación. Si se viola, indica que el diseño no cumple con una propiedad deseada.

```systemverilog
assert property(@(posedge clk) a && b);


El comportamiento de un sistema puede expresarse como una afirmación que debe ser verdadera en todo momento. Por lo tanto, las afirmaciones se utilizan para validar el comportamiento de un sistema definido como propiedades, y también pueden emplearse en la cobertura funcional.

## Properties en un diseño

Si una propiedad del diseño que se verifica mediante una aserción no se comporta como se espera, la aserción falla. Por ejemplo, supongamos que el diseño solicita una concesión y espera recibir una confirmación en los próximos cuatro ciclos. Sin embargo, si recibe una confirmación en el quinto ciclo, se viola la propiedad de que la confirmación debe devolverse en 4 ciclos y la aserción falla.

Si se prohíbe que se cumpla una propiedad del diseño que se verifica mediante una aserción, esta falla. Por ejemplo, supongamos que un procesador pequeño decodifica instrucciones leídas de la memoria, encuentra una instrucción desconocida y genera un error fatal. Si el diseño no prevé tal escenario, se viola la propiedad del diseño de que solo se pueden leer instrucciones válidas de la memoria y la aserción falla.

Como es evidente en los dos ejemplos anteriores, las propiedades de un diseño determinado se comprueban escribiendo afirmaciones SystemVerilog.

## ¿Assertions?

Podemos considerar una aserción como una representación más concisa de un Checker funcional. La funcionalidad representada por una aserción también puede escribirse como una `task` o un `Checker` de SystemVerilog que implica más líneas de código. Algunas desventajas de esto se enumeran a continuación:

- SystemVerilog es un código extenso y difícil de mantener y escalar con la cantidad de propiedades.
- Al ser un lenguaje procedimental, es difícil escribir 
- `Chekers` que involucren muchos eventos paralelos en el mismo período de tiempo.

SystemVerilog Assertions es un lenguaje declarativo utilizado para especificar condiciones temporales, es muy conciso y más fácil de mantener.

1 | // A property written in Verilog/SystemVerilog
2 | always @ (posedge clk) begin
3 |	    if (!(a && b))
4 |		   $display ("Assertion failed");
5 | end

SystemVerilog Assertions es un lenguaje declarativo utilizado para especificar condiciones temporales, es muy conciso y más fácil de mantener.

1 | // The property above written in SystemVerilog Assertions syntax
2 | assert property(@(posedge clk) a && b);