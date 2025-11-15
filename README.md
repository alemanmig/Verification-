# Verificación de Sistemas Digitales

##  Introducción
La verificación de sistemas digitales es un proceso fundamental para asegurar que un diseño implementado cumple con la intención definida en su especificación. Con el incremento en la complejidad del hardware moderno, la verificación ha evolucionado hacia metodologías avanzadas y métricas sólidas que permiten validar el comportamiento de los sistemas de forma sistemática y eficiente.

Este documento explica:
- Qué es la verificación.
- Qué es un testbench y su relación con la verificación.
- Su importancia en la industria.
- Su evolución desde Verilog hasta SystemVerilog/UVM.
- Qué es el *Functional Coverage*.
- Ejemplos prácticos en SystemVerilog.

---

##  1. ¿Qué es la Verificación?
La verificación digital es un proceso destinado a demostrar que un diseño implementa correctamente lo que la especificación establece. No consiste únicamente en crear o ejecutar testbenches, sino en un conjunto de actividades que garantizan que el sistema funciona como debe.

Actividades comunes en verificación:
- Revisión y entendimiento de especificaciones.
- Planificación de verificación.
- Creación de entornos de prueba.
- Uso de simulación, verificación formal o emulación.
- Métricas como *functional coverage* y *code coverage*.

---

##  2. ¿Qué es un Testbench?
Un **testbench** es un entorno de simulación que genera estímulos y observa respuestas del DUT (*Device Under Test*). Aunque esencial, un testbench **no es equivalente a la verificación**, sino una herramienta dentro del proceso.

### Componentes típicos de un testbench moderno
- **Driver:** envía transacciones al DUT.
- **Monitor:** captura y traduce actividad.
- **Scoreboard:** compara resultados contra un modelo de referencia.
- **Generator/Sequencer:** produce estímulos dirigidos o aleatorios.
- **Assertions (SVA):** validan propiedades temporales.

### Ejemplo básico en SystemVerilog
```systemverilog
module simple_tb;
  logic clk, rst, a, b, y;

  // Instancia del DUT
  simple_and dut (
    .clk(clk),
    .rst(rst),
    .a(a),
    .b(b),
    .y(y)
  );

  // Generación de reloj
  initial clk = 0;
  always #5 clk = ~clk;

  // Secuencia simple
  initial begin
    rst = 1;
    a = 0;
    b = 0;
    #20 rst = 0;

    a = 1; b = 0; #10;
    a = 0; b = 1; #10;
    a = 1; b = 1; #10;

    $finish;
  end
endmodule
```

---

##  3. Relación entre Verificación y Testbench
La relación puede verse como:

- **Verificación:** proceso completo que incluye planificación, estrategias, cobertura, análisis, ejecución de pruebas y testbenches.
- **Testbench:** entorno que permite aplicar estímulos, recolectar datos y validar comportamientos.

Un testbench es un instrumento; la verificación es el proceso integral.

---

##  4. Importancia de la Verificación
La verificación consume entre **60% y 80%** del esfuerzo total en un proyecto de hardware debido a:
- Costos extremadamente altos por errores en silicio.
- Complejidad creciente de los SoC modernos.
- Necesidad de confiabilidad y robustez.

Verificación insuficiente = riesgo de fallas críticas.

---

##  5. Evolución de la Verificación
### 1980-1990: Primeros años con Verilog
- Testbenches dirigidos.
- Simulación simple.
- Sin metodologías formales.

### 2000: Aparición de SystemVerilog
Incluye características esenciales:
- Clases orientadas a objetos.
- Randomización con restricciones.
- Interfaces.
- Assertions (SVA).
- Functional coverage.

### 2010 en adelante: UVM y metodologías estandarizadas
- Entornos reutilizables.
- Drivers, monitores, scoreboards y secuencias.
- Integración con verificación formal y emulación.

---

##  6. Functional Coverage
El **Functional Coverage** mide qué tan completamente se ha verificado la funcionalidad del diseño. Se enfoca en comportamientos del sistema, no en líneas de código ejecutadas.

Ejemplos:
- Estados alcanzados en una máquina de estados.
- Combinaciones específicas en interfaces.
- Casos límite.

### Ejemplo en SystemVerilog
```systemverilog
class alu_coverage;
  rand bit [3:0] op;
  rand bit [7:0] a, b;

  covergroup cg_alu @ (posedge clk);
    coverpoint op {
      bins add = {4'h0};
      bins sub = {4'h1};
      bins mul = {4'h2};
      bins div = {4'h3};
    }

    coverpoint a {
      bins low  = {[0:15]};
      bins mid  = {[16:127]};
      bins high = {[128:255]};
    }

    cross op, a;
  endgroup

  function new;
    cg_alu = new();
  endfunction
endclass
```

---

##  7. Conclusiones
La verificación digital ha crecido desde simples pruebas dirigidas hasta metodologías avanzadas como UVM. Hoy es una disciplina crítica para garantizar la calidad, funcionalidad y confiabilidad de los sistemas digitales.

El uso de cobertura funcional, testbenches estructurados y técnicas modernas permite una verificación más completa y eficiente.

---

##  8. Estructura recomendada para un repositorio Git
```text
project/
├── src/               # Código RTL
├── tb/                # Testbench y entorno de verificación
├── docs/              # Documentación y especificaciones
├── sim/               # Scripts de simulación
└── README.md          # Documento actual
```

---

##  9. Licencia
Este documento puede usarse libremente como parte de proyectos educativos, académicos o profesionales.
