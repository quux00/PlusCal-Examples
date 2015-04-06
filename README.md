# Overview

These are examples of algorithms written in PlusCal, the algorithm language for Leslie
Lamport's TLA+ algorithm specification system.

These have been created in the TLA+ Toolbox, so most of the files are supporting files
for running in the Toolbox and using the TLC algorithm verification checker.

The important (non-auto-generated) files for review are those that end in `.tla`, such
as `Euclid/Euclid.tla` and `HourClock/HourClock.tla`.

I've written the part above the line `\* BEGIN TRANSLATION` and the PlusCal code falls
between the `(*` and `*)` comment markers, starting with the `--algorithm XXX` indicator.
