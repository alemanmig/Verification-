# **Regiones de Planificación de Eventos en SystemVerilog**

---

## **Resumen**

Este documento presenta una visión formal de las *regiones de planificación de eventos* definidas en la semántica de simulación de SystemVerilog, conforme al estándar IEEE 1800-2017. El objetivo es ofrecer una explicación clara, estructurada y adecuada para cursos de diseño y verificación digital. Se incluyen descripciones conceptuales, clasificación de regiones, ejemplos en SystemVerilog y diagramas explicativos.

---

## **I. Introducción**

SystemVerilog es un lenguaje de descripción y verificación de hardware diseñado para soportar semánticas de ejecución concurrente. Debido a que una simulación digital no puede ejecutar procesos concurrentes de manera física y simultánea, el estándar IEEE define un mecanismo determinista de simulación basado en un *ciclo de eventos*, compuesto por regiones que regulan el orden de ejecución.

Estas regiones conforman la *cola de eventos* o *rueda de eventos* (**event wheel**) y aseguran que la ejecución de bloques procedurales, actualizaciones de señales, aserciones y componentes de verificación siga un orden bien definido y repetible.

---

## **II. Antecedentes y Motivación**

Las primeras versiones de Verilog incluían únicamente las regiones Active, Inactive y NBA (Non-Blocking Assignment). SystemVerilog amplió este modelo al agregar regiones específicas para la verificación, permitiendo:

* Interacciones libres de condiciones de carrera entre testbench y DUT.
* Semánticas temporales robustas para SystemVerilog Assertions (SVA).
* Observación de señales estabilizadas.
* Aislamiento entre los dominios de diseño y verificación.

---

## **III. Visión General de las Regiones de Simulación**

El ciclo de simulación se divide en una secuencia de regiones ejecutadas en orden topológico. La Tabla I resume las principales regiones.

### **Tabla I – Resumen de Regiones de Simulación**

| Región    | Propósito                                    | Constructos Típicos              |
| --------- | -------------------------------------------- | -------------------------------- |
| Preponed  | Captura valores previos a actualizaciones    | `$rose`, `$fell`, entrada SVA    |
| Active    | Ejecución procedural principal               | `always`, `initial`, `=`         |
| Inactive  | Eventos con retardo cero                     | `#0`                             |
| NBA       | Actualización de asignaciones no bloqueantes | `<=`                             |
| Observed  | Muestreo estable para SVA                    | Aserciones temporales            |
| Reactive  | Acción de aserciones y bloques de programa   | SVA action, `program`            |
| Re-NBA    | NBA generado desde lógica reactiva           | `<=` tardío                      |
| Postponed | Observación final                            | `$monitor`, `$strobe`, cobertura |

---

## **IV. Descripción Formal de Regiones**

### **A. Región Preponed**

Se ejecuta antes de cualquier actualización de señales o bloques procedurales. Usada para muestreo de valores en aserciones y comprobaciones temporales.

### **B. Región Active**

Es la región principal. Incluye la evaluación de `initial`, `always`, asignaciones bloqueantes y disparadores de sensibilidad.

### **C. Región Inactive**

Contiene procesos programados mediante `#0`. Estos procesos se ejecutan después de la región Active dentro del mismo tiempo simulado.

### **D. Región NBA (Non-Blocking Assignments)**

Las asignaciones no bloqueantes se evalúan en Active pero se aplican aquí, garantizando semánticas deterministas especialmente en lógica secuencial.

### **E. Región Observed**

Región utilizada para muestrear señales en un estado estable después de Active e Inactive. Es fundamental para SystemVerilog Assertions.

### **F. Región Reactive**

Domina la ejecución de acciones de aserciones, bloques `program` y componentes de verificación. Permite reaccionar sin generar condiciones de carrera en el DUT.

### **G. Región Re-NBA**

Procesa las asignaciones no bloqueantes generadas desde la región Reactive, manteniendo un orden consistente.

### **H. Región Postponed**

Última región del ciclo temporal actual. Permite observación final mediante `$strobe`, `$monitor` y recolección de cobertura. No se permiten modificaciones de señales.

---

## **V. Diagrama del Orden de Ejecución**

El siguiente diagrama resume el orden general de ejecución de regiones:

```
                 +---------------------------+
                 |     REGIÓN POSTPONED     |
                 +---------------------------+
                 |        REGIÓN RE-NBA      |
                 +---------------------------+
                 |         REGIÓN NBA        |
                 +---------------------------+
                 |      REGIÓN REACTIVE      |
                 +---------------------------+
                 |      REGIÓN OBSERVED      |
                 +---------------------------+
                 |   REGIÓN INACTIVE (#0)    |
                 +---------------------------+
                 |       REGIÓN ACTIVE       |
                 +---------------------------+
                 |      REGIÓN PREPONED      |
                 +---------------------------+
```

---

## **VI. Ejemplo de Interacción entre Regiones**

```systemverilog
module ejemplo_regiones;
  reg a, b, c;

  initial begin
    a = 0;
    b = 0;
    c = 0;
  end

  // Active: asignación bloqueante
  always @(a) begin
    b = a;
  end

  // NBA: asignación no bloqueante
  always @(a) begin
    c <= a;
  end

  initial begin
    a = 1;                  // Active
    #0 $display("Región Inactive");
    $strobe("Postponed: a=%0d b=%0d c=%0d", a, b, c);
  end
endmodule
```

En este ejemplo:

* `b = a` se ejecuta en Active.
* `c <= a` se programa y actualiza en NBA.
* El `#0` mueve la ejecución a Inactive.
* `$strobe` se ejecuta en Postponed, después de que las señales se estabilizan.

---

## **VII. Aplicaciones en Verificación**

Las regiones de planificación de eventos permiten:

* Evitar carreras entre DUT y testbench.
* Muestreo determinista para SVA.
* Interacción transaccional ordenada en UVM.
* Observación precisa para scoreboards y monitores.

Son un componente esencial para metodologías de verificación modernas.

---

## **VIII. Conclusiones**

Las regiones de simulación definidas por el estándar IEEE 1800-2017 proporcionan un marco determinista y robusto para simulación concurrente. Separan el dominio de diseño del de verificación, eliminan condiciones de carrera y permiten la implementación confiable de aserciones y metodologías avanzadas como UVM.

---

## **Referencias**

[1] IEEE Standard for SystemVerilog—Unified Hardware Design, Specification, and Verification Language, IEEE Std 1800-2017.
