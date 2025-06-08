LoadPackage( "FiniteCocompletions", false );
#! true
LoadPackage( "FunctorCategories", false );
#! true
q := FinQuiver( "q(a,b,c)[]" );
#! FinQuiver( "q(a,b,c)[]" )
P := PathCategory( q );
#! PathCategory( FinQuiver( "q(a,b,c)[]" ) )
Q := HomalgFieldOfRationals( );
#! Q
L := Q[P];
#! Q-LinearClosure( PathCategory( FinQuiver( "q(a,b,c)[]" ) ) )
A := AdditiveClosureOfObjectFiniteCategory_Reinterpreted( L );;
a := ObjectConstructor( A, [1,[1,0,0]] );;
b := ObjectConstructor( A, [1,[0,1,0]] );;
c := ObjectConstructor( A, [1,[0,0,1]] );;
AA := AdditiveClosure( L );;
aa := AA.a;;
bb := AA.b;;
cc := AA.c;;

# i_old := InjectionOfCofactorOfDirectSumWithGivenDirectSum( [bb,aa,bb], 1, DirectSum(aa,bb,bb) );;
# IsWellDefined(i_old);

# i := InjectionOfCofactorOfDirectSumWithGivenDirectSum( [a,b,c,a], 3, DirectSum(c,a,b,a) );;

i := ProjectionInFactorOfDirectSumWithGivenDirectSum( [b,a], 1, DirectSum(b,a) );;

IsWellDefined(i);
Display( i );
