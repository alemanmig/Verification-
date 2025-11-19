# **Rice Condition en SystemVerilog**

---

## **Resumen**

Este documento presenta una descripción formal del concepto de **condiciones de carrera** en SystemVerilog, basado en lineamientos del modelo de simulación del estándar IEEE 1800-2017. Se discuten las causas, ejemplos ilustrativos, implicaciones en simulación y diseño digital, así como metodologías para prevenirlas. Este documento está orientado a estudiantes y profesionales de verificación y diseño digital.

---

## **I. Introducción**

SystemVerilog es un lenguaje concurrente; múltiples procesos pueden ejecutarse aparentemente en paralelo. Sin embargo, los simuladores siguen un modelo de ejecución secuencial determinado por regiones de planificación de eventos (event scheduling regions). Debido a esta naturaleza concurrente simulada, pueden surgir situaciones donde el orden de actualización o lectura de señales no está garantizado, causando **condiciones de carrera**.

Las condiciones de carrera producen comportamientos no deterministas que pueden variar entre ejecuciones, simuladores o incluso dependiendo de la semilla aleatoria. Por ello, representan uno de los principales retos en simulación y verificación.

---

## **II. Definición de Condición de Carrera**

Una **condición de carrera** ocurre cuando:

> Dos o más procesos concurrentes acceden o modifican la misma variable o señal en un orden no especificado por el modelo de simulación, dando como resultado un comportamiento no determinista.

En términos prácticos: el resultado depende del orden en el que el simulador ejecuta procesos que se supone ocurren "al mismo tiempo". Cuando este orden no está definido, se produce una carrera.

---

## **III. Tipos Comunes de Condiciones de Carrera**

A continuación, se describen las formas más frecuentes de condiciones de carrera en SystemVerilog.

### **A. Carrera Write–Write (Escritura–Escritura)**

Ocurre cuando dos procesos escriben en la misma señal durante el mismo ciclo de simulación.

```systemverilog
always @(posedge clk)
  a = 1;

always @(posedge clk)
  a = 0;
```

El estándar no define cuál asignación ocurre primero. El resultado final de `a` es indeterminado.

---

### **B. Carrera Read–Write (Lectura–Escritura)**

Se produce cuando un proceso lee una señal mientras otro la escribe, sin un orden definido.

```systemverilog
always @(posedge clk)
  x = y;   // lectura de y

always @(posedge clk)
  y = x;   // escritura de y
```

Dependiendo del orden, `x` puede capturar el valor viejo o el nuevo.

---

### **C. Carrera por Asignaciones Bloqueantes**

Las asignaciones bloqueantes (`=`) se ejecutan de inmediato dentro de la región Active. Su uso en lógica secuencial puede generar carreras.

```systemverilog
always @(posedge clk)
  q = d;    // bloqueante

always @(posedge clk)
  d = q;    // bloqueante
```

---

### **D. Carrera Entre Testbench y DUT**

Muy común en entornos UVM o verificación tradicional. Sucede cuando el testbench lee o escribe señales en regiones no diseñadas para ello.

---

## **IV. Ejemplos de Comportamiento No Determinista**

```systemverilog
initial a = 0;

always @(posedge clk)
  a = a + 1;

always @(posedge clk)
  a = a + 2;
```

Dependiendo del simulador, `a` puede tomar los valores:

* 1 luego 3,
* 2 luego 3,
* incluso otros patrones dependiendo de la intercalación.

---

## **V. Modelos de Simulación Relacionados**

Las condiciones de carrera están estrechamente vinculadas al orden de ejecución de las regiones:

* **Active**: evaluaciones principales.
* **Inactive (#0)**: procesos diferidos.
* **NBA**: actualizaciones no bloqueantes.
* **Observed / Reactive**: interacción con aserciones y testbench.

Comprender estas regiones es esencial para entender por qué surgen y cómo prevenirlas.

---

## **VI. Condiciones de Carrera y su Prevención**

A continuación, se presentan métodos prácticos y formales para prevenir condiciones de carrera.

### **A. Uso Correcto de Asignaciones No Bloqueantes (`<=`)**

En lógica secuencial, todas las asignaciones deben ser `<=`.

```systemverilog
always @(posedge clk)
  q <= d;
```

Esto garantiza que todas las actualizaciones suceden en la región NBA, evitando carreras.

---

### **B. Evitar Múltiples Drivers sobre la Misma Señal**

Una señal **no** debe ser asignada por múltiples bloques `always`.

### **C. Separación Clara entre DUT y Testbench**

El testbench debe reaccionar usando:

* **Observed Region** (muestreo limpio)
* **Reactive Region** (acciones libres de carreras)

### **D. No Mezclar `=` y `<=` en el Mismo Dominio Secuencial**

Regla clásica:

> *Asignaciones secuenciales → `<=`*
> *Asignaciones combinacionales → `=`*

### **E. Evitar `#0` Arbitrarios**

Los `#0` mueven procesos a Inactive y pueden introducir carreras difíciles de depurar.

### **F. Estructura Recomendada en UVM/Testbench**

* Lectura de señales: Observed
* Actualización o estímulo: Reactive
* No modificar señales del DUT en Active

### **G. Uso de Interfaces con Modports**

Los `modport` pueden restringir qué señales son leídas o escritas por cada componente.

---

## **VII. Conclusión**

Las condiciones de carrera representan uno de los principales retos en simulación digital debido a su naturaleza no determinista. Dominar su identificación y eliminación es esencial para asegurar que el diseño y el testbench interactúen de manera consistente y reproducible. Las técnicas y prácticas descritas en este documento permiten evitar estos problemas en sistemas complejos y entornos UVM.

---

## **Referencias**

[1] IEEE Standard for SystemVerilog—Unified Hardware Design, Specification, and Verification Language, IEEE Std 1800-2017.
