LoadPackage( "FunctorCategories", false );

# (m,s) <= (m',s') <= (m'',s'')

q := "q(m,mp,s,sp,svmp,spwm,mpp,spp,spvmpp,sppwmp)\
[mp-svmp:mp->svmp,m-svmp:m->svmp,s-svmp:s->svmp,spwm-m:spwm->m,spwm-s:spwm->s,spwm-sp:spwm->sp,\
# mpp-spvmpp:mpp->spvmpp,mp-spvmpp:mp->spvmpp,sp-spvmpp:sp->spvmpp,sppwmp-mp:sppwmp->mp,sppwmp-sp:sppwmp->sp,sppwmp-spp:sppwmp->spp]";;

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true );; # Add partial meet and partial join operations to P?

# Splash( DotVertexLabelledDigraph( P,
#                                   [ [ P.m, P.mp, P.s, P.sp, P.svmp, P.spwm, P.mpp, P.spp, P.spvmpp, P.sppwmp ] ],
#                                   [ "orange", "blue" ] ) );


###########################################################################################################


Display( "[x] Created the poset");
DisplayTimer( "Time" );
StartTimer( "Time" );

excluded_meets := Concatenation( Arrangements( [ P.s, P.m ], 2 ),
                                 Arrangements( [ P.s, P.sp ], 2 ),
                                 Arrangements( [ P.s, P.m, P.svmp ], 3 ),
                                 Arrangements( [ P.s, P.sp, P.svmp ], 3 ),
                                 
                                 Arrangements( [ P.sp, P.mp ], 2 ),
                                 Arrangements( [ P.sp, P.spp ], 2 ),
                                 Arrangements( [ P.spp, P.spvmpp ], 2 ),
                                 
                                 Arrangements( [ P.m, P.spvmpp ], 2 ),
                                 Arrangements( [ P.s, P.spvmpp ], 2 ),
                                 Arrangements( [ P.svmp, P.spp ], 2 )
                                 
                                 );;

excluded_joins := Concatenation( Arrangements( [ P.m, P.s ], 2 ),
                                 Arrangements( [ P.m, P.mp ], 2 ),
                                 Arrangements( [ P.mp, P.m, P.spwm ], 3 ),
                                 Arrangements( [ P.m, P.s, P.spwm ], 3 ),
                                 
                                 Arrangements( [ P.sp, P.mp ], 2 ),
                                 Arrangements( [ P.mp, P.mpp ], 2 ),
                                 Arrangements( [ P.mpp, P.sppwmp ], 2 ),
                                 
                                 Arrangements( [ P.spwm, P.mpp ], 2 ),
                                 Arrangements( [ P.m, P.sppwmp ], 2 ),
                                 Arrangements( [ P.s, P.sppwmp ], 2 )
                                 
                                 );;

relative_prime_filters := RelativePrimeFiltersOfPoset( P, excluded_meets, excluded_joins );;

Display( "[x] Found all relative prime filters")
DisplayTimer( "Time" );
StartTimer( "Time" );

distributive_extension := UpSetsAsDistributiveExtension( relative_prime_filters );;

Display( "[x] Found all upsets of relative prime filters")
DisplayTimer( "Time" );
StartTimer( "Time" );

# set1 ∈ set_of_sets
contains := { set_of_sets, set1 } -> ForAny( set_of_sets, set2 -> ForAll( set2, el -> el in set1 ) and
                                                                  ForAll( set1, el -> el in set2 ) );;

# filter1 ⊂ filter2
check_if_subset := { filter1, filter2 } -> ForAll( filter1,
                                                   f -> contains( filter2, f ) );; # ∀f ∈ filter1 :  f ∈ filter2

digraph := Digraph( distributive_extension, check_if_subset );
digraph := DigraphReflexiveTransitiveReduction(digraph);

vertices := DigraphVertices( digraph );

for vertex in vertices do
  
  position := Position( vertices, vertex );
  
  SetDigraphVertexLabel( digraph, position, String( position ) ) ;
  
od;

for obj in SetOfObjects( P ) do
  
  position := Position( distributive_extension, EmbeddingInDistributiveExtension( relative_prime_filters, obj ) );
  
  SetDigraphVertexLabel( digraph, position,
                         ReplacedStringViaRecord( ObjectLabel( UnderlyingCell( obj ) ), rec( p := "'", v := "∨", w := "∧" ) ) ) ;
  
od;

digraph := DotVertexLabelledDigraph( digraph );

Splash( digraph );

Display( "[x] Created the digraph of the distributive extension")
DisplayTimer( "Time" );
StopTimer( "Time" );
