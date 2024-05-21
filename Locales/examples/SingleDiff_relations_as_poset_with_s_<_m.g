LoadPackage( "FunctorCategories", false );

# (m,s) <= (m',s') and s<=m, s'<=m'

q := "q(m,mp,s,sp,svmp,spwm)\[s-m:s->m,sp-mp:sp->mp,mp-svmp:mp->svmp,m-svmp:m->svmp,s-svmp:s->svmp,spwm-m:spwm->m,spwm-s:spwm->s,spwm-sp:spwm->sp]";;

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

# Recall s' ∧ m <= s

forbidden_meets := Concatenation( Arrangements( [ P.s, P.mp ], 2 ),
                                  Arrangements( [ P.s, P.mp, P.m ], 3 ),
                                  Arrangements( [ P.s, P.mp, P.svmp ], 3 ),
                                  Arrangements( [ P.s, P.mp, P.m, P.svmp ], 4 ),
                                 
                                  Arrangements( [ P.m, P.mp ], 2 ),
                                  Arrangements( [ P.m, P.mp, P.svmp ], 3 ) );;

excluded_meets := NewDictionary( IsList, false );
for meet in forbidden_meets do
    
    AddDictionary( excluded_meets, meet );
    
od;

# Recall m <= s ∨ m'

forbidden_joins := Concatenation( Arrangements( [ P.m, P.sp ], 2 ),
                                  Arrangements( [ P.m, P.sp, P.s ], 3 ),
                                  Arrangements( [ P.m, P.sp, P.spwm ], 3 ),
                                  Arrangements( [ P.m, P.sp, P.s, P.spwm ], 4 ),
                                 
                                  Arrangements( [ P.s, P.sp ], 2 ),
                                  Arrangements( [ P.s, P.sp, P.spwm ], 3 ) );;

excluded_joins := NewDictionary( IsList, false );
for join in forbidden_joins do
    
    AddDictionary( excluded_joins, join );
    
od;

relative_prime_filters := RelativePrimeFiltersOfPoset( P, excluded_meets, excluded_joins );;

Display( "[x] Found all relative prime filters");
StartTimer( "Time" );
DisplayTimer( "Time" );

# Draw the poset of relative prime filters
contains := { set1, set2 } -> ForAll( set1, s -> s in set2 );;

digraph := Digraph( relative_prime_filters, contains );;
digraph := DigraphReflexiveTransitiveReduction( digraph );;

NameOfRelativePrimeFilter :=
  function( filter )
    local name, element;
    
    name := "{ ";
    
    for element in filter do
        
        Append( name, ReplacedStringViaRecord( ObjectLabel( UnderlyingCell( element ) ), rec( p := "'", v := "∨", w := "∧" ) ) );
        Append( name, ", " );
        
    od;
    
    Remove( name, Length( name ) );
    Remove( name, Length( name ) );
    Append( name, " }");
    
    return name;
    
  end;

vertices := DigraphVertices( digraph );;

for vertex in vertices do
  
  position := Position( vertices, vertex );
  
  SetDigraphVertexLabel( digraph, position, NameOfRelativePrimeFilter( relative_prime_filters[ position ] ) ) ;
  
od;

digraph := DotVertexLabelledDigraph( digraph );
digraph := ReplacedStringViaRecord( digraph, rec( node := "rankdir = \"BT\"\nnode" ) );

Splash( digraph );

# Distributive extension

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
 
digraph := Digraph( distributive_extension, check_if_subset );;
digraph := DigraphReflexiveTransitiveReduction(digraph);;

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
digraph := ReplacedStringViaRecord( digraph, rec( node := "rankdir = \"BT\"\nnode" ) );

Splash( digraph );
