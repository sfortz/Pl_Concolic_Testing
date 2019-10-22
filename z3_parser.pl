:- module(z3_parser,[pterm/3]).

pterm(S,S_,T) :- %% Functors 
    string_codes("(",OPENING_BRACKET), 
    string_codes(" ",SPACE), 
    string_codes(")",CLOSING_BRACKET),
    append(OPENING_BRACKET,S2,S),!,
    pid(S2,S3,Fl),
    atom_codes(F,Fl),
    append(SPACE,S4,S3),
    ptermseq(S4,S5,Args),
    append(CLOSING_BRACKET,S_,S5),
    T =.. [F|Args]. %% term reconstruction
pterm(S,S_,T) :- 
    pid(S,S_,Idl),
    read_term_from_atom(Idl,T,[variable_names(_)]).
    %writeln(out-read_term_from_atom(Idl,T,[variable_names(VarNames)])).
    
ptermseq(S,S_,[T1|TR]) :-
    pterm(S,S2,T1),
    string_codes(" ",SPACE), 
    append(SPACE,S3,S2),!,
    ptermseq(S3,S_,TR).
ptermseq(S,S_,[T]) :-
    pterm(S,S_,T).

%% valid identifier
pid(S,S_,Id) :- pid(S,S_,[],Id).
pid([H|R],Rest,Id_,Id) :- % rest id
  pvalido(H), !,
  append(Id_,[H],Id2), 
  pid(R,Rest,Id2,Id).
pid(S,S,Id,Id). % end id

% numbers, letter, etc
psymbol(A) :- A=95 ; A=34 ; A=39 ; A=96. %% _ ' " `
pnum(A) :- 48 =< A, A =< 57.        % 48 = '0', 57 = '9'
pmayus(A) :- 65 =< A, A =< 90.      % 65 = 'A', 90 = 'Z'
pminus(A) :- 97 =< A, A =< 122.     % 97 = 'a', 122 = 'z'
pletra(A) :- pminus(A) ; pmayus(A).
pvalido(A) :- pletra(A) ; pnum(A) ; psymbol(A).

