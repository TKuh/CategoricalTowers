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
# P := PosetOfCategory( F : find_meets_and_joins := true );

###########################################################################################################

#     t
#    / \
#   c   d
#  / \ /
# a   b
#  \ /
#   i

# q := "q(i,a,b,c,d,t)\
# [ia:i->a,ib:i->b,\
# ac:a->c, bc:b->c,\
# bd:b->d,\
# ct:c->t,dt:d->t]";;

# q := FinQuiver( q );;
# F := PathCategory( q );;
# P := PosetOfCategory( F : find_meets_and_joins := true );
# M := MeetSemilatticeOfSingleDifferences( L );;

# Splash( DotVertexLabelledDigraph( M, [ [ M.i, M.a, M.b, M.c, M.d, M.t ], SetOfGeneratingObjects( M ) ], [ "orange", "blue", "magenta" ] ) );

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

# q := "q(i,a,b,c,d,e,f,t)\
# [ia:i->a,ib:i->b,\
# ac:a->c, bc:b->c, bd:b->d,\
# ce:c->e, de:d->e, df:d->f,\
# et:e->t,ft:f->t]";;

# q := FinQuiver( q );;
# F := PathCategory( q );;
# P := PosetOfCategory( F : find_meets_and_joins := true );;
# M := MeetSemilatticeOfSingleDifferences( L );;

# Splash( DotVertexLabelledDigraph( M,
#                                   [ [ M.i, M.a, M.b, M.c, M.d, M.e, M.f, M.t ],
#                                     SetOfGeneratingObjects( M ),
#                                     [ SingleDifference( M, [ L.d, L.c ] ),
#                                       SingleDifference( M, [ L.e, L.b ] ) ] ],
#                                   [ "orange", "blue", "magenta", "green" ] ) );


###########################################################################################################

# Linear order

q := "q(i,a,b,c,d,e,f,g,h,t)\
[ia:i->a,ab:a->b,bc:b->c,cd:c->d,de:d->e,ef:e->f,fg:f->g,gh:g->h,ht:h->t]";;

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true );;

Display("[x] Poset");

M := MeetSemilatticeOfSingleDifferences( L );;

Splash( DotVertexLabelledDigraph( M,
                                  [ [ M.i, M.a, M.b, M.c, M.d, M.e, M.f, M.g, M.h, M.t ],
                                    SetOfGeneratingObjects( M ),
                                    [ SingleDifference( M, [ L.t, L.a ] ),
                                      SingleDifference( M, [ L.t, L.b ] ),
                                      SingleDifference( M, [ L.t, L.c ] ),
                                      SingleDifference( M, [ L.t, L.d ] ),
                                      SingleDifference( M, [ L.t, L.e ] ),
                                      SingleDifference( M, [ L.t, L.f ] ),
                                      SingleDifference( M, [ L.t, L.g ] ),
                                      SingleDifference( M, [ L.t, L.h ] ) ] ],
                                  [ "orange", "blue", "green", "magenta" ] ) );
