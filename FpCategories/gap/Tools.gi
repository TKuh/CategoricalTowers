# SPDX-License-Identifier: GPL-2.0-or-later
# FpCategories: Finitely presented categories by generating quivers and relations
#
# Implementations
#

##
InstallTrueMethod( IsObjectFiniteCategory, IsFinitelyPresentedCategory );

##
InstallMethod( SetOfGeneratingMorphisms,
        [ IsInitialCategory ],
        
  function( I )
    
    return [ ];
    
end );

##
InstallMethodForCompilerForCAP( SetOfGeneratingMorphisms,
        "for a quotient category",
        [ IsQuotientCapCategory ],
        
  function( cat )
    
    return SetOfGeneratingMorphismsOfCategory( cat );
    
end );

##
InstallMethod( SetOfGeneratingMorphismsAsUnresolvableAttribute,
        [ IsCapCategory ],
        
  SetOfGeneratingMorphismsOfCategory );

##
InstallOtherMethod( Size,
        "for a CAP category",
        [ IsCapCategory and HasSetOfObjects and HasRangeCategoryOfHomomorphismStructure ],
        
  function( C )
    local H, objs;
    
    H := RangeCategoryOfHomomorphismStructure( C );
    
    if not IsSkeletalCategoryOfFiniteSets( H ) then
        TryNextMethod( );
    fi;
    
    objs := SetOfObjects( C );
    
    return Sum( objs, s ->
                Sum( objs, t ->
                     Length( HomStructure( s, t ) ) ) );
    
end );

##
CAP_INTERNAL_ADD_REPLACEMENTS_FOR_METHOD_RECORD(
        rec(
            YonedaEmbeddingData :=
            [ [ "HomomorphismStructureOnObjects", 2 ], ## called in List
              [ "IdentityMorphism", 3 ], ## called alone and in List
              [ "HomomorphismStructureOnMorphismsWithGivenObjects", 4 ] ] ## called in List twice
            )
);

##
InstallMethodForCompilerForCAP( YonedaEmbeddingData,
        [ IsCapCategory and HasDefiningTripleOfUnderlyingQuiver and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( C )
    local defining_triple, nr_objs, nr_mors, arrows, objs, mors, Yoneda_on_objs, Yoneda_on_mors;
    
    defining_triple := DefiningTripleOfUnderlyingQuiver( C );
    
    nr_objs := defining_triple[1];
    nr_mors := defining_triple[2];
    arrows := defining_triple[3];
    
    objs := SetOfObjects( C );
    
    mors := SetOfGeneratingMorphisms( C );
    
    Yoneda_on_objs :=
      function ( obj )
        local Yobj_on_objs, id_obj, Yobj_on_mors;
        
        Yobj_on_objs := List( [ 0 .. nr_objs - 1 ], o ->
                              HomomorphismStructureOnObjects( C,
                                      objs[1 + o],
                                      obj ) );
        
        id_obj := IdentityMorphism( C, obj );
        
        Yobj_on_mors := List( [ 0 .. nr_mors - 1 ], m ->
                              HomomorphismStructureOnMorphismsWithGivenObjects( C,
                                      Yobj_on_objs[1 + arrows[1 + m][2]],
                                      mors[1 + m],
                                      id_obj,
                                      Yobj_on_objs[1 + arrows[1 + m][1]] ) );
        
        return Pair( Yobj_on_objs, Yobj_on_mors );
        
    end;
    
    Yoneda_on_mors :=
      function ( source_on_objs, mor, target_on_objs )
        
        return List( [ 0 .. nr_objs - 1 ], o ->
                     HomomorphismStructureOnMorphismsWithGivenObjects( C,
                             source_on_objs[1 + o],
                             IdentityMorphism( C, objs[1 + o] ),
                             mor,
                             target_on_objs[1 + o] ) );
        
    end;
    
    return Pair( Yoneda_on_objs, Yoneda_on_mors );
    
end );

##
CAP_INTERNAL_ADD_REPLACEMENTS_FOR_METHOD_RECORD(
        rec(
            CoYonedaEmbeddingData :=
            [ [ "HomomorphismStructureOnObjects", 2 ], ## called in List
              [ "IdentityMorphism", 3 ], ## called alone and in List
              [ "HomomorphismStructureOnMorphismsWithGivenObjects", 4 ] ] ## called in List twice
            )
);

##
InstallMethodForCompilerForCAP( CoYonedaEmbeddingData,
        [ IsCapCategory and HasDefiningTripleOfUnderlyingQuiver and HasRangeCategoryOfHomomorphismStructure ],
        
  function ( C )
    local defining_triple, nr_objs, nr_mors, arrows, objs, mors, coYoneda_on_objs, coYoneda_on_mors;
    
    defining_triple := DefiningTripleOfUnderlyingQuiver( C );
    
    nr_objs := defining_triple[1];
    nr_mors := defining_triple[2];
    arrows := defining_triple[3];
    
    objs := SetOfObjects( C );
    
    mors := SetOfGeneratingMorphisms( C );
    
    coYoneda_on_objs :=
      function ( obj )
        local Yobj_on_objs, id_obj, Yobj_on_mors;
        
        Yobj_on_objs := List( [ 0 .. nr_objs - 1 ], o ->
                              HomomorphismStructureOnObjects( C,
                                      obj,
                                      objs[1 + o] ) );
        
        id_obj := IdentityMorphism( C, obj );
        
        Yobj_on_mors := List( [ 0 .. nr_mors - 1 ], m ->
                              HomomorphismStructureOnMorphismsWithGivenObjects( C,
                                      Yobj_on_objs[1 + arrows[1 + m][1]],
                                      id_obj,
                                      mors[1 + m],
                                      Yobj_on_objs[1 + arrows[1 + m][2]] ) );
        
        return Pair( Yobj_on_objs, Yobj_on_mors );
        
    end;
    
    coYoneda_on_mors :=
      function ( source_on_objs, mor, target_on_objs )
        
        return List( [ 0 .. nr_objs - 1 ], o ->
                     HomomorphismStructureOnMorphismsWithGivenObjects( C,
                             target_on_objs[1 + o],
                             mor,
                             IdentityMorphism( C, objs[1 + o] ),
                             source_on_objs[1 + o] ) );
        
    end;
    
    return Pair( coYoneda_on_objs, coYoneda_on_mors );
    
end );

if IsPackageMarkedForLoading( "Digraphs", ">= 1.3.1" ) then

##
InstallMethod( QuiverStringOfDigraph,
               [ IsDigraph, IsString, IsString ],
               
  function( digraph, name, mor )
    local string, vertices, label, labels, mors;
    
    string := [ name, "(" ];
    
    vertices := DigraphVertices( digraph );
    
    label :=
      function( vertex )
        local str;
        
        str := String( DigraphVertexLabel( digraph, vertex ) );
        
        if First( str ) = '(' and Last( str ) = ')' then
            str := str{[ 2 .. Length( str ) - 1 ]};
        fi;
        
        return str;
        
    end;
    
    labels := List( vertices, label );
    
    Append( string, [ JoinStringsWithSeparator( labels, "," ), ")[" ] );
    
    mors :=
      function( s )
        local targets;
        
        targets := OutNeighborsOfVertex( digraph, s );
        
        if DuplicateFreeList( targets ) = targets then
            return List( targets, t ->
                         Concatenation( mor, "_", String( s ), "_", String( t ), ":", labels[s], "->", labels[t] ) );
        else
            return List( [ 1 .. Length( targets ) ], i ->
                         Concatenation( mor, "_", String( s ), "_", String( targets[i] ), "_", String( i ), ":", labels[s], "->", labels[targets[i]] ) );
        fi;
        
    end;
    
    Append( string, [ JoinStringsWithSeparator( Concatenation( List( [ 1 .. Length( vertices ) ], mors ) ), "," ), "]" ] );
    
    return Concatenation( string );
    
end );

fi;
