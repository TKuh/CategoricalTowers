#! @BeginChunk PrecompileAdelmanCategoryOfAdditiveClosureOfAlgebroid

#! @Example

LoadPackage( "Algebroids", false );
#! true
LoadPackage( "CompilerForCAP", false );
#! true

QQ := HomalgFieldOfRationals( );;
snake_quiver := RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" );;
A := PathAlgebra( QQ, snake_quiver );;
A_bar := QuotientOfPathAlgebra( A, [ A.abc ] );;

ReadPackage( "Algebroids", "gap/CompilerLogic.gi" );
#! true

# only valid for the construction above
# FIXME: IsInt should be IsRat, but specializations of types are not yet supported by CompilerForCAP
# this might already have been added by PrecompileAdditiveClosureOfAlgebroid.g
if not IsBound( CAP_JIT_INTERNAL_TYPE_SIGNATURES.CoefficientsOfPaths ) then CapJitAddTypeSignature( "CoefficientsOfPaths", [ IsList, IsPathAlgebraElement ], rec( filter := IsList, element_type := rec( filter := IsInt ) ) ); fi;
#CapJitAddTypeSignature( "CoefficientsOfPaths", [ IsList, IsQuotientOfPathAlgebraElement ], rec( filter := IsList, element_type := rec( filter := IsInt ) ) ); fi;

precompile_AdelmanCategoryOfAdditiveClosureOfAlgebroid := function( Rq, over_Z, path_algebra, ring )
    CapJitPrecompileCategoryAndCompareResult(
        EvalString( ReplacedString( """Rq -> AdelmanCategory( AdditiveClosure( Algebroid(
            Rq, over_Z : FinalizeCategory := true
        ) : FinalizeCategory := true ) )""", "over_Z", String( over_Z ) ) ),
        [ Rq ],
        "Algebroids",
        Concatenation(
            "AdelmanCategoryOfAdditiveClosureOfAlgebroidOfFiniteDimensional",
            path_algebra,
            "OfRightQuiverOver",
            ring,
            "Precompiled"
        ) :
        operations := [
            "IsZeroForMorphisms",
            "CokernelProjection",
            "IsDominating",
            "IsEqualAsSubobjects",
        ]
    ); end;;

#precompile_AdelmanCategoryOfAdditiveClosureOfAlgebroid( A, false, "PathAlgebra", "Field" );
#precompile_AdelmanCategoryOfAdditiveClosureOfAlgebroid( A_bar, false, "QuotientOfPathAlgebra", "Field" );
precompile_AdelmanCategoryOfAdditiveClosureOfAlgebroid( A, true, "PathAlgebra", "Z" );
#precompile_AdelmanCategoryOfAdditiveClosureOfAlgebroid( A_bar, true, "QuotientOfPathAlgebra", "Z" );

AdelmanCategoryOfAdditiveClosureOfAlgebroidOfFiniteDimensionalPathAlgebraOfRightQuiverOverZPrecompiled( A );
#! Adelman category( Additive closure( Algebroid( Z, FreeCategory(
#! RightQuiver( "q(4)[a:1->2,b:2->3,c:3->4]" ) ) ) ) )

#! @EndExample

#! @EndChunk
