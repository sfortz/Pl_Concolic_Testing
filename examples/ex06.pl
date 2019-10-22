depth( true, 0 ).
depth( (_g1,_gs), _depth ) :-
    depth( _g1, _depth_g1 ),
    depth( _gs, _depth_gs ),
    max( _depth_g1, _depth_gs, _depth ).
depth( _goal, s(_depth) ) :-
    prog_clause( _goal, _body ),
    depth( _body, _depth ).

max( _num, 0, _num ).
max( 0, s(_num), s(_num) ).
max( s(_x), s(_y), s(_max) ) :-
    max( _x, _y, _max ).

prog_clause( member( X, Xs ), append( _, [X|_], Xs ) ).
prog_clause( append( [], L, L ), true ).
prog_clause( append( [X|L1], L2, [X|L3] ), append( L1, L2, L3 ) ).
