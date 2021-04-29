# SCAM
The implementation of the Strong Crumbling Abstract Machine (SCAM) for the Strong Call-by-value lambda-calculus. The machine is described in the paper
B. Accattoli, A. Condoluci, C. Sacerdoti Coen, "Strong Call-by-Value is Reasonable, Implosively", presented at LICS 2021.

Web interface
=============

What does it do:
 It allows the user to write down a lamba-term in the browser and it
 shows the state of the machine after every step. Be aware of diverging terms!

Dependencies for the Web interface:
 * dune (a package manager for ocaml; it installs ocaml as well)
 * the js_of_ocaml dune package (obtained via "dune install js_of_ocaml")

How to compile the Web interface:
 dune build

How to execute the Web interface:
 point your browser to _build/default/index.html

Command line interface
======================

What does it do:  
 It runs a fixed set of tests, printing out the state of the machine after
 each execution. More tests can be added by duplicating the last line of
 strong_cbv.ml, which is

         `parse "x (y. (z.z) (z.z))" print_and_eval`

 The command line interface does not allow to enter lambda-terms interactively

Dependencies for the command-line interface:
 * ocaml

How to compile the command-line tests:  
 `make`

How to execute the command-line tests:  
 `./strong_cbv`
