
contains( Pat, Str ) :- con( Str, ([],Pat) ).

con( _, (_,[]) ).
con( [T|Rem_str], Pat_info ) :-
    new( T, Pat_info, New_pat_info ),
    con( Rem_str, New_pat_info ).

new( T, (Prefix,[T|Rem_postfix]), (New_prefix,Rem_postfix) ) :-
    append( Prefix, [T], New_prefix ).
new( T, (Prefix,[Dift|Rem_postfix]), (New_prefix,New_postfix) ) :-
    T \== Dift,
    append( Prefix, [T], Temp ),
    append( New_prefix, Rest, Prefix ),
    append( _, New_prefix, Temp ),
    append( Rest, [Dift|Rem_postfix], New_postfix ).

append( [], L, L ).
append( [X|Xs], Ys, [X|Zs] ) :- append( Xs, Ys, Zs ).

