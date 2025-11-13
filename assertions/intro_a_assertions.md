# Aserciones en SystemVerilog

## Objetivo

Esta guía presenta los fundamentos de las aserciones en SystemVerilog, incluyendo sus tipos, sintaxis, aplicaciones y diferencias semánticas. Está diseñada para apoyar la formación de estudiantes en verificación funcional y formal de sistemas digitales.

---

## 1️.0. ¿Qué son las aserciones?

Las **aserciones** son instrucciones que permiten verificar si el comportamiento de un sistema digital es el esperado. Se utilizan principalmente para:

- Validar el diseño durante la simulación.
- Detectar errores en los estímulos de entrada.
- Medir cobertura funcional.

---

## 1.1. Tipos de aserciones

En SystemVerilog existen dos tipos principales de aserciones:

- Aserciones inmediatas (`immediate assertions`)
- Aserciones concurrentes (`concurrent assertions`)


### 🔹 Aserciones inmediatas (`immediate assertions`)

Las aserciones inmediatas se ejecutan como instrucciones dentro de bloques procedimentales (`always`, `initial`, etc.) y siguen la semántica de eventos de simulación. Esto significa que se evalúan en el momento exacto en que ocurre un cambio en las señales involucradas.

- Se ejecutan como instrucciones dentro de bloques procedimentales (`always`, `initial`).
- Siguen la **semántica de eventos**: se evalúan en el instante en que ocurre un cambio.
- Se usan principalmente en simulación.
- No existe una versión restrictiva de este tipo.

**Sintaxis:**
```systemverilog
assert (expresión) else $error("mensaje de error");

Ejemplo:

always_ff @(posedge clk) begin
  enable <= 1;
  assert (enable) else $error("La señal enable no está activa");
end
```

** 🔹 Aserciones concurrentes (concurrent assertions)

- Se basan en la semántica de reloj: evalúan propiedades temporales sincronizadas con `clk`.
- Utilizan sequence y property.
- Compatibles con simulación y verificación formal.
- Permiten describir comportamientos secuenciales.
  
Uno de los objetivos de SystemVerilog es ofrecer una semántica común que permita usar estas aserciones en distintas herramientas de diseño y verificación. Por ejemplo, las herramientas de verificación formal analizan el circuito usando una semántica basada en ciclos, donde los eventos entre flancos de reloj se simplifican o se abstraen.
Las aserciones concurrentes están diseñadas para adaptarse a esta forma de evaluación, lo que facilita el análisis formal. Sin embargo, en algunos casos, esta abstracción puede generar diferencias respecto a la evaluación tradicional basada en eventos.

**Sintaxis:**
```systemverilog

sequence nombre_secuencia;
  evento1 ##n evento2;
endsequence

property nombre_propiedad;
  @(posedge clk) disable iff (reset) nombre_secuencia;
endproperty

assert property (nombre_propiedad)
  else $error("mensaje de error");
  ```

**Ejemplo:**
```systemverilog

sequence req_ack;
  req ##1 ack;
endsequence
}
property p_req_ack;
  @(posedge clk) disable iff (reset) req_ack;
endproperty

assert property (p_req_ack)
  else $error("ack no llegó después de req");
  
```