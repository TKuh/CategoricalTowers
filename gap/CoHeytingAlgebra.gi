# SPDX-License-Identifier: GPL-2.0-or-later
# Locales: Locales, frames, coframes, meet semi-lattices of locally closed subsets, and Boolean algebras of constructible sets
#
# Implementations
#

InstallValue( CAP_INTERNAL_COHEYTING_ALGEBRAS_BASIC_OPERATIONS, rec( ) );

##
CAP_INTERNAL_COHEYTING_ALGEBRAS_BASIC_OPERATIONS.ConegationOnMorphisms :=
  [ [ "ConegationOnMorphismsWithGivenConegations", 1 ],
    [ "ConegationOnObjects", 2 ] ];

##
InstallMethod( ConegationOnMorphisms,
               [ IsCapCategoryMorphism ],
        
  function( morphism )
    
    return ConegationOnMorphismsWithGivenConegations(
                   ConegationOnObjects( Range( morphism ) ),
                   morphism,
                   ConegationOnObjects( Source( morphism ) ) );
    
end );

CAP_INTERNAL_ADD_REPLACEMENTS_FOR_METHOD_RECORD( CAP_INTERNAL_COHEYTING_ALGEBRAS_BASIC_OPERATIONS );

##
InstallGlobalFunction( ADD_COMMON_METHODS_FOR_COHEYTING_ALGEBRAS,
  function( coheyting_algebra )
    
    SetIsCocartesianCoclosedCategory( coheyting_algebra, true );
    
    ADD_COMMON_METHODS_FOR_LATTICES( coheyting_algebra );
    
    ## The cocartesian monoidal structure
    
    ## The coclosedness of the cocartesian monoidal structure
    
    ##
    AddCoexponentialOnMorphismsWithGivenCoexponentials( coheyting_algebra,
      function( cat, S, alpha, beta, R )
        
        return UniqueMorphism( S, R );
        
    end );
    
    ##
    AddCocartesianEvaluationMorphismWithGivenRange( coheyting_algebra,
      function( cat, A, B, BxCoex_A_B )
        
        return UniqueMorphism( A, BxCoex_A_B );
        
    end );
    
    ##
    AddCocartesianCoevaluationMorphismWithGivenSource( coheyting_algebra,
      function( cat, A, B, Coex_AxB_A)
        
        return UniqueMorphism( Coex_AxB_A, B );
        
    end );
    
    ##
    AddCoproductToCoexponentialAdjunctionMap( coheyting_algebra,
      function( cat, B, C, g )
        local A;
        
        A := Source( g );
        
        return UniqueMorphism( CoexponentialOnObjects( A, B ), C );
        
    end );
    
    ##
    AddCoexponentialToCoproductAdjunctionMap( coheyting_algebra,
      function( cat, A, B, f )
        local C, BC;
        
        C := Range( f );
        
        BC := Coproduct( B, C );
        
        return UniqueMorphism( A, BC);
        
    end );
    
    ##
    AddCocartesianPreCoComposeMorphismWithGivenObjects( coheyting_algebra,
      function( cat, Coex_A_C, A, B, C, Coex_A_BxCoex_B_C);
        
        return UniqueMorphism( Coex_A_C, Coex_A_BxCoex_B_C );
        
    end );
    
    ##
    AddCocartesianPostCoComposeMorphismWithGivenObjects( coheyting_algebra,
      function( cat, Coex_A_C, A, B, C, Coex_B_CxCoex_A_B );
        
        return UniqueMorphism( Coex_A_C, Coex_B_CxCoex_A_B );
        
    end );
    
    ##
    AddCoexponentialCoproductCompatibilityMorphismWithGivenObjects( coheyting_algebra,
      function( cat, source, L, range )
        
        return UniqueMorphism( source, range );
        
    end );
    
    ## The co-negation
    
    ##
    AddMorphismFromDoubleConegationWithGivenDoubleConegation( coheyting_algebra,
      function( cat, A, B )
        
        return UniqueMorphism( A, B );
        
    end );
    
end );

##
InstallMethod( StableInternalCoHom,
        "for two objects in a thin category",
        [ IsObjectInThinCategory, IsObjectInThinCategory ],

  function( V, W )
    local V_W;
    
    V_W := V;
    
    repeat
        V := V_W;
        V_W := InternalCoHomOnObjects( V_W, W );
    until AreIsomorphicForObjectsIfIsHomSetInhabited( V_W, V );
    
    return V_W;
    
end );
