# Pipeline-Register-with-Valid-Ready-Handshake-SystemVerilog-
The pipeline-reg module acts as a single-entry buffer between an upstream producer and a downstream consumer.
Overview

This project implements a 1-stage pipeline register using the standard valid–ready handshake protocol, commonly used in streaming interfaces such as AXI-Stream.
The design ensures lossless data transfer, supports back-to-back transactions, and correctly handles downstream back-pressure.
A self-checking SystemVerilog testbench and a SystemVerilog Assertion (SVA) are included to verify correct functionality and guarantee that no data is dropped or corrupted.

Design Description:
The pipeline_reg module acts as a single-entry buffer between an upstream producer and a downstream consumer.

Key Features:
32-bit wide data path, Standard valid–ready handshake, Supports back-to-back transfers, Handles downstream stalls safely, No data loss or overwrite,Synchronous design with active-low asynchronous reset
