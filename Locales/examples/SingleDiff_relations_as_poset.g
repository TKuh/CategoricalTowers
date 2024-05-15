LoadPackage( "FunctorCategories", false );

# (m,s) <= (m',s')

q := "q(m,mp,s,sp,svmp,spwm)\[x:mp->svmp,y:m->svmp,z:s->svmp,q:spwm->m,j:spwm->s,w:spwm->sp]";;

StartTimer( "Time" );

q := FinQuiver( q );;
F := PathCategory( q );;
P := PosetOfCategory( F : find_meets_and_joins := true );;

Splash( DotVertexLabelledDigraph( P,
                                  [ [ P.m, P.mp, P.s, P.sp, P.svmp, P.spwm ] ],
                                  [ "orange", "blue" ] ) );

Display( "[x] Created the poset");
DisplayTimer( "Time" );
StartTimer( "Time" );

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

Display( "[x] Found all relative prime filters");
StartTimer( "Time" );
DisplayTimer( "Time" );

distributive_extension := UpSetsAsDistributiveExtension( relative_prime_filters );;

Display( "[x] Found all upsets of relative prime filters");
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

Display( "[x] Created the digraph of the distributive extension");
DisplayTimer( "Time" );
StopTimer( "Time" );

vertices := DigraphVertices( digraph );

# Rename all vertices to numbers
for vertex in vertices do
  
  position := Position( vertices, vertex );
  
  SetDigraphVertexLabel( digraph, position, String( position ) ) ;
  
od;

# Rename vertices corresponding to element of P via their names in P
for obj in SetOfObjects( P ) do
  
  position := Position( distributive_extension, EmbeddingInDistributiveExtension( relative_prime_filters, obj ) );
  
  SetDigraphVertexLabel( digraph, position,
                         ReplacedStringViaRecord( ObjectLabel( UnderlyingCell( obj ) ), rec( p := "'", v := "∨", w := "∧" ) ) ) ;
  
od;

digraph := DotVertexLabelledDigraph( digraph );

Splash( digraph );
