LoadPackage( "FunctorCategories", false );

#   t
#  /|\
# d | e
# | | |
# | c |
# |/ \|
# a   b
#  \ /
#   i

# Not distributive because of:  d x (a v e) != (d x a) v (d x e)

# q := "q(i,a,b,c,d,e,t)\
# [ia:i->a,ib:i->b,\
# ac:a->c,ad:a->d,\
# bc:b->c,be:b->e,\
# dt:d->t,ct:c->t,et:e->t]";;

# q := FinQuiver( q );;
# F := PathCategory( q );;
# P := PosetOfCategory( F : find_meets_and_joins := true, check_distributivity := true );

# Splash( DotVertexLabelledDigraph( P, [ [ P.i, P.a, P.b, P.c, P.d, P.e, P.t ] ], [ "orange", "blue" ] ) );


###########################################################################################################


#     t
#    / \
#   c   d
#  / \ /
# a   b
#  \ /
#   i

q := "q(i,a,b,c,d,t)\
[ia:i->a,ib:i->b,\
ac:a->c, bc:b->c,\
bd:b->d,\
ct:c->t,dt:d->t]";;

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true, check_distributivity := true );
M := MeetSemilatticeOfSingleDifferences( P );;

Splash( DotVertexLabelledDigraph( M, [ [ M.i, M.a, M.b, M.c, M.d, M.t ], SetOfGeneratingObjects( M ) ], [ "orange", "blue", "magenta" ] ) );


###########################################################################################################


#       t
#      / \
#     e   f
#    / \ /
#   c   d
#  / \ /
# a   b
#  \ /
#   i

q := "q(i,a,b,c,d,e,f,t)\
[ia:i->a,ib:i->b,\
ac:a->c, bc:b->c, bd:b->d,\
ce:c->e, de:d->e, df:d->f,\
et:e->t,ft:f->t]";;

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true, check_distributivity := true );;
M := MeetSemilatticeOfSingleDifferences( P );;

Splash( DotVertexLabelledDigraph( M,
                                  [ [ M.i, M.a, M.b, M.c, M.d, M.e, M.f, M.t ],
                                    SetOfGeneratingObjects( M ),
                                    [ SingleDifference( M, [ P.d, P.c ] ),
                                      SingleDifference( M, [ P.e, P.b ] ) ] ],
                                  [ "orange", "blue", "magenta", "green" ] ) );


###########################################################################################################


# Linear order

# i < a < b < c < d < e < f < g < h < t

q := "q(i,a,b,c,d,e,f,g,h,t)\
[ia:i->a,ab:a->b,bc:b->c,cd:c->d,de:d->e,ef:e->f,fg:f->g,gh:g->h,ht:h->t]";;

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true, check_distributivity := true );;
M := MeetSemilatticeOfSingleDifferences( P );;

Splash( DotVertexLabelledDigraph( M,
                                  [ [ M.i, M.a, M.b, M.c, M.d, M.e, M.f, M.g, M.h, M.t ],
                                    SetOfGeneratingObjects( M ),
                                    [ SingleDifference( M, [ P.t, P.a ] ),
                                      SingleDifference( M, [ P.t, P.b ] ),
                                      SingleDifference( M, [ P.t, P.c ] ),
                                      SingleDifference( M, [ P.t, P.d ] ),
                                      SingleDifference( M, [ P.t, P.e ] ),
                                      SingleDifference( M, [ P.t, P.f ] ),
                                      SingleDifference( M, [ P.t, P.g ] ),
                                      SingleDifference( M, [ P.t, P.h ] ) ] ],
                                  [ "orange", "blue", "green", "magenta" ] ) );
