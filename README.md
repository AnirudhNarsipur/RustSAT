This repo contains two branches:

- julia: A DPLL SAT solver in Julia I wrote as a part of a grad CS course (CSCI2951O Prescriptive Analytics) at Brown Univeristy.
- main

I decided to finally learn Rust and decided to write a SAT solver as a first project. Highlights are:

- Conflict Driven Clause Learning (CDCL) + non chronological backtracking
- 2 watched literals
- VSIDS heuristic
- clause deletion
- random restarts

I plan to eventually: 
 - add proof generation support
 - Fix any lingering bugs + broken test suite
 - Improve efficiency

I'll hopefully eventually get around to exploring some graph based ideas in parallel solving.
