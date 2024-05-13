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
# P := PosetOfCategory( F );;
# L := AddPossibleLatticeOperations( P );;
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
# L := AddPossibleLatticeOperations( P );;
# M := MeetSemilatticeOfSingleDifferences( L );;

# Splash( DotVertexLabelledDigraph( M,
#                                   [ [ M.i, M.a, M.b, M.c, M.d, M.e, M.f, M.t ],
#                                     SetOfGeneratingObjects( M ),
#                                     [ SingleDifference( M, [ L.d, L.c ] ),
#                                       SingleDifference( M, [ L.e, L.b ] ) ] ],
#                                   [ "orange", "blue", "magenta", "green" ] ) );


###########################################################################################################

# Linear order

# q := "q(i,a,b,c,d,e,f,g,h,t)\
# [ia:i->a,ab:a->b,bc:b->c,cd:c->d,de:d->e,ef:e->f,fg:f->g,gh:g->h,ht:h->t]";;

# q := FinQuiver( q );;
# F := PathCategory( q );;
# P := PosetOfCategory( F );;
# L := AddPossibleLatticeOperations( P );;
# M := MeetSemilatticeOfSingleDifferences( L );;

# Splash( DotVertexLabelledDigraph( M,
#                                   [ [ M.i, M.a, M.b, M.c, M.d, M.e, M.f, M.g, M.h, M.t ],
#                                     SetOfGeneratingObjects( M ),
#                                     [ SingleDifference( M, [ L.t, L.a ] ),
#                                       SingleDifference( M, [ L.t, L.b ] ),
#                                       SingleDifference( M, [ L.t, L.c ] ),
#                                       SingleDifference( M, [ L.t, L.d ] ),
#                                       SingleDifference( M, [ L.t, L.e ] ),
#                                       SingleDifference( M, [ L.t, L.f ] ),
#                                       SingleDifference( M, [ L.t, L.g ] ),
#                                       SingleDifference( M, [ L.t, L.h ] ) ] ],
#                                   [ "orange", "blue", "green", "magenta" ] ) );
#! @EndExample


###########################################################################################################


# (m,s) <= (m',s') <= (m'',s'')

# q := "q(a,b,c,d,bvc,awd)\[x:a->bvc,y:awd->b]";

q := "q(m,mp,s,sp,svmp,spwm)\[x:mp->svmp,y:m->svmp,z:s->svmp,q:spwm->m,j:spwm->s,w:spwm->sp]";;

# q := "q(m,mp,s,sp,svmp,spwm,mpp,spp,spvmpp,sppwmp)\
# [mp-svmp:mp->svmp,m-svmp:m->svmp,s-svmp:s->svmp,spwm-m:spwm->m,spwm-s:spwm->s,spwm-sp:spwm->sp,\
# # mpp-spvmpp:mpp->spvmpp,mp-spvmpp:mp->spvmpp,sp-spvmpp:sp->spvmpp,sppwmp-mp:sppwmp->mp,sppwmp-sp:sppwmp->sp,sppwmp-spp:sppwmp->spp]";;

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true );; # Add partial meet and partial join operations to P?


###########################################################################################################


Display( "[x] Created the poset");

excluded_meets := Concatenation( Arrangements( [ P.s, P.m ], 2 ),
                                 Arrangements( [ P.s, P.sp ], 2 ),
                                 Arrangements( [ P.s, P.m, P.svmp ], 3 ),
                                 Arrangements( [ P.s, P.sp, P.svmp ], 3 ),
                                 Arrangements( [ P.sp, P.svmp ], 2 ) );;

excluded_joins := Concatenation( Arrangements( [ P.m, P.s ], 2 ),
                                 Arrangements( [ P.m, P.mp ], 2 ),
                                 Arrangements( [ P.mp, P.m, P.spwm ], 3 ),
                                 Arrangements( [ P.m, P.s, P.spwm ], 3 ),
                                 Arrangements( [ P.mp, P.spwm ], 2 ) );;

relative_prime_filters := RelativePrimeFiltersOfPoset( P, excluded_meets, excluded_joins );;

Display( "[x] Found all relative prime filters")

# set1 ∈ set_of_sets
contains := { set_of_sets, set1 } -> ForAny( set_of_sets, set2 -> ForAll( set2, el -> el in set1 ) and
                                                                  ForAll( set1, el -> el in set2 ) );;

# filter1 ⊂ filter2
check_if_subset := { filter1, filter2 } -> ForAll( filter1,
                                                   f -> contains( filter2, f ) );; # ∀f ∈ filter1 :  f ∈ filter2

distributive_extension := UpSetsAsDistributiveExtension( relative_prime_filters );;

Display( "[x] Found all upsets of relative prime filters")

digraph := Digraph( distributive_extension, check_if_subset );
digraph := DigraphReflexiveTransitiveReduction(digraph);

vertices := DigraphVertices( digraph );

for vertex in vertices do
  
  position := Position( vertices, vertex );
  
  SetDigraphVertexLabel( digraph, position, String( position ) ) ;
  
od;

for obj in SetOfObjects( P ) do
  
  position := Position( distributive_extension, EmbeddingInDistributiveExtension( relative_prime_filters, obj ) );
  
  # Display(position);
  # Display(ObjectLabel( UnderlyingCell( obj ) ) );
  
  SetDigraphVertexLabel( digraph, position,
                         ReplacedStringViaRecord( ObjectLabel( UnderlyingCell( obj ) ), rec( p := "'", v := "∨", w := "∧" ) ) ) ;
  
od;

# digraph := DotVertexLabelledDigraph( digraph );

Splash( digraph );

Display( "[x] Created the digraph of the distributive extension")

Splash( DotVertexLabelledDigraph( P,
                                  [ [ P.m, P.mp, P.s, P.sp, P.svmp, P.spwm ] ],
                                  [ "orange", "blue" ] ) );

# Splash( DotVertexLabelledDigraph( P,
#                                   [ [ P.m, P.mp, P.s, P.sp, P.svmp, P.spwm, P.mpp, P.spp, P.spvmpp, P.sppwmp ] ],
#                                   [ "orange", "blue" ] ) );