/**
 * Sample TLA+ modules and outputs for testing
 */

export const VALID_TLA_MODULE = `---- MODULE Sample ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Spec == Init /\\ [][Next]_x
====`;

export const SIMPLE_TLA_MODULE = `---- MODULE Simple ----
VARIABLE state
Init == state = "initial"
Next == state' = "next"
====`;

export const SANY_SUCCESS_XML = `<?xml version="1.0" encoding="UTF-8"?>
<modules>
  <module name="Sample">
    <constants></constants>
    <variables><variable>x</variable></variables>
  </module>
</modules>`;

export const SANY_ERROR_OUTPUT = `Parsing failed at line 5: Unexpected token`;

export const TLC_SUCCESS_OUTPUT = [
  'TLC2 Version 2.18',
  'Running breadth-first search...',
  'Model checking completed. No error has been found.',
  'States found: 10',
  'Distinct states: 10'
];

export const TLC_VIOLATION_OUTPUT = [
  'TLC2 Version 2.18',
  'Error: Invariant Inv is violated.',
  'The behavior up to this point is:',
  'State 1: x = 0',
  'State 2: x = 1'
];

export const TLC_SIMULATION_OUTPUT = [
  'TLC2 Version 2.18',
  'Running Random Simulation...',
  'Generated 100 states in 3 seconds.',
  'No violations found.'
];

export const TLC_EXPLORE_OUTPUT = [
  'TLC2 Version 2.18',
  'State 1:',
  '/\\ x = 0',
  'State 2:',
  '/\\ x = 1',
  'State 3:',
  '/\\ x = 2'
];
