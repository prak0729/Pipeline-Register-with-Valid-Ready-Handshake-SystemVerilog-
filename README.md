# Pipeline-Register-with-Valid-Ready-Handshake-SystemVerilog-
The pipeline-reg module acts as a single-entry buffer between an upstream producer and a downstream consumer.
Overview

This project implements a 1-stage pipeline register using the standard valid–ready handshake protocol, commonly used in streaming interfaces such as AXI-Stream.
The design ensures lossless data transfer, supports back-to-back transactions, and correctly handles downstream back-pressure.

A self-checking SystemVerilog testbench and a SystemVerilog Assertion (SVA) are included to verify correct functionality and guarantee that no data is dropped or corrupted.

Design Description

The pipeline_reg module acts as a single-entry buffer between an upstream producer and a downstream consumer.

Key Features

32-bit wide data path

Standard valid–ready handshake

Supports back-to-back transfers

Handles downstream stalls safely

No data loss or overwrite

Synchronous design with active-low asynchronous reset

Interface Signals
Input Signals
Signal	Width	Description
clk	1	Clock signal
rstn	1	Active-low asynchronous reset
in_valid	1	Indicates valid input data
in_data	32	Input data bus
out_ready	1	Indicates downstream readiness
Output Signals
Signal	Width	Description
in_ready	1	Indicates pipeline readiness to accept input
out_valid	1	Indicates valid output data
out_data	32	Output data bus
Handshake Protocol
Input Transfer

An input transaction occurs when:

in_valid && in_ready


This means the upstream has valid data and the pipeline is ready to accept it.

Output Transfer

An output transaction occurs when:

out_valid && out_ready


This means valid data is available and the downstream is ready to receive it.

Internal Operation

data_reg stores the data currently held in the pipeline stage.

valid_reg indicates whether the pipeline contains valid data.

The pipeline can accept new data when:

It is empty, or

The current data is being accepted by the downstream in the same cycle.

assign in_ready = ~valid_reg || out_ready;


This logic enables flow-through operation, allowing one data item to exit while another enters in the same clock cycle.

Testbench Description

The testbench (tb_pipeline_reg) verifies the design under multiple scenarios:

Reset behavior

Normal data transfer

Back-to-back input transactions

Downstream stalling (out_ready = 0)

Data retention during stalls

Resume after back-pressure

Monitoring

The testbench prints messages on every successful transfer:

Input transfer: in_valid && in_ready

Output transfer: out_valid && out_ready

Assertion-Based Verification

A SystemVerilog assertion is used to ensure no data loss or corruption.

Assertion Intent

Every accepted input must eventually appear at the output

Output data must match the original input

Data must remain stable until it is accepted by the downstream

property no_data_loss;
  @(posedge clk)
  disable iff (!rstn)
  (in_valid && in_ready)
    |=> (out_valid && out_data == $past(in_data))
    until (out_ready);
endproperty


If the assertion fails, an error is reported:

Data loss detected!

Simulation Instructions

Compile the design and testbench:

vlog pipeline_reg.sv


Run the simulation:

vsim tb_pipeline_reg
run -all


Observe the console output and assertion results.

Expected Output Behavior

Data is transferred only when both valid and ready are asserted

No data is overwritten during downstream stalls

All input data appears at the output in the correct order

Assertion passes with no errors

Applications

This design pattern is widely used in:

AXI-Stream pipelines

FIFO front-end registers

RTL datapath staging

High-throughput SoC designs

Flow-controlled interfaces
