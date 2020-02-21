# Concolic Testing with SWIPrologZ3

##### This tool aims at performing concolic testing on Prolog programs.
##### Concolic testing uses concrete execution to guide symbolic execution.

##### The Microsoft's SMT solver Z3 is used in order to solve constraints: https://github.com/Z3Prover/z3
##### To interact with this solver, we used a new version of the SWIPrologZ3 interface, first developed by: https://github.com/mistupv/SWIPrologZ3.
##### Thanks to them for their work. The big news compared to their version is the support of constraints over Prolog terms.

![Implementation workflow.](https://github.com/sfortz/Pl_Concolic_Testing/blob/master/tool_arch.pdf)

### Installation of the SWIPrologZ3 interface

##### Simple SWI Prolog API for Microsoft's SMT solver Z3

First, you should install SWI Prolog and the SMT solver Z3 (https://github.com/Z3Prover/z3).
It has been tested with SWI Prolog version 8.0.3 and Z3 version 4.8.7.

Then, you can download or clone the repository, e.g.,

````$ git clone https://github.com/sfortz/Pl_Concolic_Testing.git````

and compile the C source file using the SWI Prolog utility program ````swipl-ld```` and the ````fpic```` option, as follows:

````$ swipl-ld -fpic -c swiplz3.c````

````$ swipl-ld -shared -o swiplz3 swiplz3.o -lz3````

Now, you can use the Z3 functions by loading the file ```swiplz3.pl```. For this purpose, you can add

````:- use_module(swiplz3).````

to your Prolog file.

### Installation of the concolic tool

##### Concolic testing tool for Prolog, using the Microsoft's SMT solver Z3

** interactive mode **

1) run SWI Prolog
   > swipl

2) load in the program, e.g.,

   > ['concolic_tool'].

3) try some of the predefined tests, e.g.,

   > cex1.
   > cex2.
   > ...

** command mode **

0) comment/uncomment the cgi-bin parts (search for cgi-bin)

1) run SWI Prolog
   > swipl

2) load in the contest program, e.g.,

   > ['concolic_tool'].

3) save a stand alone executable, e.g.,

   ?- qsave_program('concolic_tool',[stand_alone(true),goal((main,halt))]).

   [take care! the executable is platform dependent and since it is
   in the dropbox folder, you could need to recompile it when moving
   from one machine to another one...]

4) exit from SWI Prolog and use it from the command line, e.g,

   > ./concolic_tool -cg "p(s(a))" -ground "[1]" -depth "2" -timeout "10" -file "examples/ex01.pl"

   Note that only atomic initial goals are allowed (w.l.o.g)
