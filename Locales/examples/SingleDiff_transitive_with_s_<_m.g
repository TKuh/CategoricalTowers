LoadPackage( "FunctorCategories", false );

# (m,s) <= (m',s') <= (m'',s'') and s<=m, s'<=m', s''<=m''

q := "q(m,mp,s,sp,svmp,spwm,mpp,spp,spvmpp,sppwmp)\
[spwm-s:spwm->s,spwm-sp:spwm->sp,s-m:s->m,sp-mp:sp->mp,m-svmp:m->svmp,mp-svmp:mp->svmp,\
sppwmp-sp:sppwmp->sp,sppwmp-spp:sppwmp->spp,sp-mp:sp->mp,spp-mpp:spp->mpp,mp-spvmpp:mp->spvmpp,mpp-spvmpp:mpp->spvmpp]";

q := FinQuiver( q );;
F := PathCategory( q );;

StartTimer( "Time" );

P := PosetOfCategory( F : find_meets_and_joins := true );;

# Splash( DotVertexLabelledDigraph( P,
#                                   [ [ P.m, P.mp, P.s, P.sp, P.svmp, P.spwm, P.mpp, P.spp, P.spvmpp, P.sppwmp ] ],
#                                   [ "orange", "blue" ] ) );


###########################################################################################################


Display( "[x] Created the poset");
DisplayTimer( "Time" );
StartTimer( "Time" );

forbidden_meets := Concatenation( # Right side
                                  Arrangements( [ P.s, P.sp ], 2 ),
                                  Arrangements( [ P.s, P.sp, P.mp ], 3 ),
                                  Arrangements( [ P.s, P.sp, P.svmp ], 3 ),
                                  Arrangements( [ P.s, P.sp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.s, P.sp, P.mp, P.spvmpp ], 4 ),
                                  Arrangements( [ P.s, P.sp, P.mp, P.svmp ], 4 ),
                                  Arrangements( [ P.s, P.sp, P.mp, P.svmp, P.spvmpp ], 5 ),
                                  Arrangements( [ P.s, P.mp ], 2 ),
                                  Arrangements( [ P.s, P.mp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.s, P.mp, P.svmp ], 3 ),
                                  Arrangements( [ P.s, P.mp, P.m ], 3 ),
                                  Arrangements( [ P.s, P.mp, P.spvmpp, P.svmp ], 4 ),
                                  Arrangements( [ P.s, P.mp, P.spvmpp, P.m ], 4 ),
                                  Arrangements( [ P.s, P.mp, P.svmp, P.m ], 4 ),
                                  Arrangements( [ P.s, P.mp, P.spvmpp, P.svmp, P.m ], 5 ),
                                  Arrangements( [ P.s, P.spvmpp ], 2 ),
                                  Arrangements( [ P.s, P.spvmpp, P.svmp ], 3 ),
                                  Arrangements( [ P.s, P.spvmpp, P.m ], 3 ),
                                  Arrangements( [ P.s, P.spvmpp, P.svmp, P.m ], 4 ),
                                  
                                  Arrangements( [ P.m, P.mp ], 2 ),
                                  Arrangements( [ P.m, P.spvmpp ], 2 ),
                                  Arrangements( [ P.m, P.mp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.m, P.mp, P.svmp ], 3 ),
                                  Arrangements( [ P.m, P.spvmpp, P.svmp ], 3 ),
                                  Arrangements( [ P.m, P.mp, P.spvmpp, P.svmp ], 4 ),
                                  
                                  Arrangements( [ P.svmp, P.spp ], 2 ),
                                  Arrangements( [ P.svmp, P.mpp ], 2 ),
                                  Arrangements( [ P.svmp, P.spvmpp ], 2 ),
                                  Arrangements( [ P.svmp, P.spp, P.mpp ], 3 ),
                                  Arrangements( [ P.svmp, P.spp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.svmp, P.mpp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.svmp, P.spp, P.mpp, P.spvmpp ], 4 ),
                                  
                                  # Left side
                                  Arrangements( [ P.sp, P.spp ], 2 ),
                                  Arrangements( [ P.sp, P.spp, P.mpp ], 3 ),
                                  Arrangements( [ P.sp, P.spp, P.svmp ], 3 ),
                                  Arrangements( [ P.sp, P.spp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.sp, P.spp, P.mpp, P.spvmpp ], 4 ),
                                  Arrangements( [ P.sp, P.spp, P.mpp, P.svmp ], 4 ),
                                  Arrangements( [ P.sp, P.spp, P.svmp, P.spvmpp ], 4 ),
                                  Arrangements( [ P.sp, P.spp, P.mpp, P.svmp, P.spvmpp ], 5 ),
                                  Arrangements( [ P.sp, P.mpp ], 2 ),
                                  Arrangements( [ P.sp, P.mpp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.sp, P.mpp, P.svmp ], 3 ),
                                  Arrangements( [ P.sp, P.mpp, P.mp ], 3 ),
                                  Arrangements( [ P.sp, P.mpp, P.spvmpp, P.svmp ], 4 ),
                                  Arrangements( [ P.sp, P.mpp, P.spvmpp, P.mp ], 4 ),
                                  Arrangements( [ P.sp, P.mpp, P.svmp, P.mp ], 4 ),
                                  Arrangements( [ P.sp, P.mpp, P.spvmpp, P.svmp, P.mp ], 5 ),
                                  
                                  Arrangements( [ P.mp, P.mpp ], 2 ),
                                  Arrangements( [ P.mp, P.mpp, P.spvmpp ], 3 ),
                                  Arrangements( [ P.mp, P.mpp, P.svmp ], 3 ),
                                  Arrangements( [ P.mp, P.mpp, P.spvmpp, P.svmp ], 4 )
                                  
                                 );;

excluded_meets := NewDictionary( IsList, false );
for meet in forbidden_meets do
    
    AddDictionary( excluded_meets, meet );
    
od;

forbidden_joins := Concatenation( # Right side
                                  Arrangements( [ P.m, P.mp ], 2 ),
                                  Arrangements( [ P.m, P.mp, P.sp ], 3 ),
                                  Arrangements( [ P.m, P.mp, P.spwm ], 3 ),
                                  Arrangements( [ P.m, P.mp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.m, P.mp, P.sp, P.sppwmp ], 4 ),
                                  Arrangements( [ P.m, P.mp, P.sp, P.spwm ], 4 ),
                                  Arrangements( [ P.m, P.mp, P.sp, P.spwm, P.sppwmp ], 5 ),
                                  Arrangements( [ P.m, P.sp ], 2 ),
                                  Arrangements( [ P.m, P.sp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.m, P.sp, P.spwm ], 3 ),
                                  Arrangements( [ P.m, P.sp, P.s ], 3 ),
                                  Arrangements( [ P.m, P.sp, P.sppwmp, P.spwm ], 4 ),
                                  Arrangements( [ P.m, P.sp, P.sppwmp, P.s ], 4 ),
                                  Arrangements( [ P.m, P.sp, P.spwm, P.s ], 4 ),
                                  Arrangements( [ P.m, P.sp, P.sppwmp, P.spwm, P.s ], 5 ),
                                  Arrangements( [ P.m, P.sppwmp ], 2 ),
                                  Arrangements( [ P.m, P.sppwmp, P.spwm ], 3 ),
                                  Arrangements( [ P.m, P.sppwmp, P.s ], 3 ),
                                  Arrangements( [ P.m, P.sppwmp, P.spwm, P.s ], 4 ),
                                  
                                  Arrangements( [ P.s, P.sp ], 2 ),
                                  Arrangements( [ P.s, P.sppwmp ], 2 ),
                                  Arrangements( [ P.s, P.sp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.s, P.sp, P.spwm ], 3 ),
                                  Arrangements( [ P.s, P.sppwmp, P.spwm ], 3 ),
                                  Arrangements( [ P.s, P.sp, P.sppwmp, P.spwm ], 4 ),
                                  
                                  Arrangements( [ P.spwm, P.mpp ], 2 ),
                                  Arrangements( [ P.spwm, P.spp ], 2 ),
                                  Arrangements( [ P.spwm, P.sppwmp ], 2 ),
                                  Arrangements( [ P.spwm, P.mpp, P.spp ], 3 ),
                                  Arrangements( [ P.spwm, P.mpp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.spwm, P.spp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.spwm, P.mpp, P.spp, P.sppwmp ], 4 ),
                                  
                                  # Left side
                                  Arrangements( [ P.mp, P.mpp ], 2 ),
                                  Arrangements( [ P.mp, P.mpp, P.spp ], 3 ),
                                  Arrangements( [ P.mp, P.mpp, P.spwm ], 3 ),
                                  Arrangements( [ P.mp, P.mpp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.mp, P.mpp, P.spp, P.sppwmp ], 4 ),
                                  Arrangements( [ P.mp, P.mpp, P.spp, P.spwm ], 4 ),
                                  Arrangements( [ P.mp, P.mpp, P.spwm, P.sppwmp ], 4 ),
                                  Arrangements( [ P.mp, P.mpp, P.spp, P.spwm, P.sppwmp ], 5 ),
                                  Arrangements( [ P.mp, P.spp ], 2 ),
                                  Arrangements( [ P.mp, P.spp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.mp, P.spp, P.spwm ], 3 ),
                                  Arrangements( [ P.mp, P.spp, P.sp ], 3 ),
                                  Arrangements( [ P.mp, P.spp, P.sppwmp, P.spwm ], 4 ),
                                  Arrangements( [ P.mp, P.spp, P.sppwmp, P.sp ], 4 ),
                                  Arrangements( [ P.mp, P.spp, P.spwm, P.sp ], 4 ),
                                  Arrangements( [ P.mp, P.spp, P.sppwmp, P.spwm, P.sp ], 5 ),
                                  
                                  Arrangements( [ P.sp, P.spp ], 2 ),
                                  Arrangements( [ P.sp, P.spp, P.sppwmp ], 3 ),
                                  Arrangements( [ P.sp, P.spp, P.spwm ], 3 ),
                                  Arrangements( [ P.sp, P.spp, P.sppwmp, P.spwm ], 4 )
                                  
                                 );;

excluded_joins := NewDictionary( IsList, false );
for join in forbidden_joins do
    
    AddDictionary( excluded_joins, join );
    
od;

relative_prime_filters := RelativePrimeFiltersOfPoset( P, excluded_meets, excluded_joins );;

Display( "[x] Found all relative prime filters");
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

StartTimer( "Time" );
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
digraph := ReplacedStringViaRecord( digraph, rec( node := "rankdir = \"BT\"\nnode" ) );

Splash( digraph );

Display( "[x] Created the digraph of the distributive extension")
DisplayTimer( "Time" );
StopTimer( "Time" );


#################################################################################################################################


quit();

# Proof that m <= s ∨ m'' and s'' ∧ m <= s

# gap> Display( relative_prime_filters );
# [ [ An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (m), An object in the poset given by: (s), 
#       An object in the poset given by: (svmp) ], 
#   [ An object in the poset given by: (spp), An object in the poset given by: (mpp),
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (mp), An object in the poset given by: (sp), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (mp), An object in the poset given by: (svmp),
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (m), An object in the poset given by: (mp), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (m), An object in the poset given by: (s), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (mp), An object in the poset given by: (sp), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (m), An object in the poset given by: (mp), 
#       An object in the poset given by: (s), An object in the poset given by: (svmp)
#         , An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (m), An object in the poset given by: (s), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (spp), 
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (spwm), An object in the poset given by: (m), 
#       An object in the poset given by: (mp), An object in the poset given by: (s), 
#       An object in the poset given by: (sp), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (mp), 
#       An object in the poset given by: (sppwmp), 
#       An object in the poset given by: (sp), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (spp), 
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ], 
#   [ An object in the poset given by: (spwm), An object in the poset given by: (m), 
#       An object in the poset given by: (mp), An object in the poset given by: (s), 
#       An object in the poset given by: (sp), 
#       An object in the poset given by: (svmp), 
#       An object in the poset given by: (mpp), 
#       An object in the poset given by: (spvmpp) ] ]




# Proof that m <= s ∨ m''

up_m := EmbeddingInDistributiveExtension( relative_prime_filters, P.m ); # ↑{ { m, s, s∨m' } }
up_s := EmbeddingInDistributiveExtension( relative_prime_filters, P.s ); # ↑{ { s } }
up_mpp := EmbeddingInDistributiveExtension( relative_prime_filters, P.mpp ); # ↑{ ... }
up_s_v_up_mpp := DuplicateFreeList( Concatenation( up_s, up_mpp ) ); # ↑{ ... }
check_if_subset( up_m, up_s_v_up_mpp );

# Proof that s'' ∧ m <= s

intersect := function( upset1, upset2 ) return Filtered( upset1, element -> element in upset2 ); end;

up_spp := EmbeddingInDistributiveExtension( relative_prime_filters, P.spp ); # ↑{ { s'' } }
up_spp_w_up_m := intersect( up_spp, up_m ); # ↑{ { m, s, s∨m', s'' } }
check_if_subset( up_spp_w_up_m, up.s ); # ↑{ { m, s, s∨m', s'' } } ⊂ ↑{ { s } }

