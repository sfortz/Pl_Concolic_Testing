CONTEST:

** current stable version **

contest.v7.pl

** interactive mode **

1) run SWI Prolog
   > swipl

2) load in the program, e.g.,

   > ['contest.v1.07'].

3) try some of the predefined tests, e.g.,

   > cex1.
   > cex2.
   > ...

** command mode **

0) comment/uncomment the cgi-bin parts (search for cgi-bin)

1) run SWI Prolog
   > swipl 

2) load in the contest program, e.g.,

   > ['contest.v1.07'].

3) save a stand alone executable, e.g.,

   ?- qsave_program('contest',[stand_alone(true),goal((main,halt))]).

   [take care! the executable is platform dependent and since it is
   in the dropbox folder, you could need to recompile it when moving
   from one machine to another one...]

4) exit from SWI Prolog and use it from the command line, e.g,

   > ./contest -cg "p(s(a))" -ground "[1]" -depth "2" -timeout "10" -file "examples/ex01.pl"

   Note that only atomic initial goals are allowed (w.l.o.g)
