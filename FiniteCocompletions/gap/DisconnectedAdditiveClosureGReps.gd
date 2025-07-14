# SPDX-License-Identifier: GPL-2.0-or-later
# FiniteCocompletions: Finite (co)product/(co)limit (co)completions
#
# Declarations
#

#! @Chapter Disconnected additive closure for GReps

#! @BeginChunk DisconnectedAddClosureGRepsIntroduction

#! Let $C$ be a pre-additive category with finitely many objects.
#! Instead of representing a direct sum as as list
#! of integer multiplicities of fixed length
#! (see Chapter <Ref Chap="Chapter_AdditiveClosureObjectFinite" />,
#! and Chapter <Ref Chap="Chapter_AdditiveClosureOfObjectFiniteDisconnectedCategory" />)
#! we can also represent a direct sum by tuples consisting of
#! an integer multiplicity and an object in the underlying category.
#! 
#! For example, assume all the objects of $C$ are $\{ S_1, S_2, S_3, S_4 \}$ satisfying
#! $\mathrm{Hom}_C(S_i, S_j) = \{ 0_{ij} \}$ for $i \neq j$.
#! An object in <C>AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps</C> would be
#! $[ [4, S_1], [2, S_2], [6, S_4] ]$ representing a direct sum
#! $S_1^4 \oplus S_2^2 \oplus S_4^6$.
#! 
#! The ordering of the tuples is important and is determined by the order of
#! the underlying objects of $C$.
#! For example $[ [2, S_4], [4, S_1] ]$ is not valid, since the tuple
#! $[2, S_4]$ appears before $[4, S_1]$, but $S_1$ has a smaller index than $S_4$
#! in <C>SetOfObjectsOfCategory</C>( $C$ ).
#! Additionally, each object $S_i$ **must** appear at most once inside a tuple.
#! 
#! The morphisms are the same as those of <C>AdditiveClosureOfObjectFiniteDisconnectedCategory</C>
#! (see Chapter <Ref Chap="Chapter_AdditiveClosureOfObjectFiniteDisconnectedCategory" />),
#! i.e., a morphism is a list of matrices of morphisms in $C$. In particular,
#! there must be a matrix for every underlying object, even if it is a zero matrix.
#! 
#! If $C$ is skeletal, then the disconnected additive closure for GReps is also skeletal.

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The GAP category of disconnected additive closures for GReps of object finite Ab-categories 
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps", IsCapCategory );

#! @Description
#!  The GAP category of objects in disconnected additive closures for GReps of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps", IsCapCategoryObject );

#! @Description
#!  The GAP category of morphisms in disconnected additive closures for GReps of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps", IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  The argument is an object finite pre-additive category $C$. The output is its disconnected additive closure for GReps $C^\oplus$.
#! @Arguments C
#! @Returns the category $C^{\oplus}$
DeclareAttribute( "AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps", IsCapCategory );

#! @Description
#!  Same as <Ref Attr="AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps" Label="for IsCapCategory" />, but as an operation instead of an attribute.
#! @Arguments C
#! @Returns the category $C^\oplus$
DeclareOperation( "DISCONNECTED_ADDITIVE_CLOSURE_GREPS", [ IsCapCategory ] );

if false then
#! @Description
#! The input is a disconnected additive closure for GReps <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps(</C> $A$ <C>)</C>
#! of an object finite pre-additive category <A>A</A> and a list of tuples of the format
#! $[ [ m_i, S_i ], \dots, [ m_j, S_j ] ]$ representing a direct sum $S_i^{m_i} \oplus \dots \oplus S_j^{m_j}$ where
#! * $S_i, \dots, S_j$ are objects in the underlying category;
#! * $m_i, ..., m_j$ are integers representing the multiplicties.
#! The tuples **must** be ordered via: $(m_i, S_i)$ appears before $(m_j, S_j)$ if and only if the index of
#! $S_i$ in <C>SetOfObjectsOfCategory</C>( $C$ ) is less than the index of $S_j$
#! Each object $S_i$ must appear **at most** once inside a tuple.
#! See also <Ref Attr="MultiplicitiesAndObjects" Label="for IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps" />.
#! @Arguments DAC, l
#! @Returns a &CAP; category object
DeclareOperation( "ObjectConstructor", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsList ] );

#! @Description
#! The input is a disconnected additive closure for GReps <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps(</C> $A$ <C>)</C>
#! of an object finite pre-additive category <A>A</A>,
#! * <A>s</A> is the source object,
#! * <A>list_of_matrices</A> is a list of lists of lists of morphisms in A,
#! * <A>t</A> is the target object.
#! There must be a matrix for **every** underlying object, even if it is a zero matrix.
#! See also <Ref Attr="ListOfMatrices" Label="for IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps" />.
#! @Arguments DAC, s, list_of_matrices, t
#! @Returns a &CAP; category morphism
DeclareOperation( "MorphismConstructor", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsList ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#! The argument is an object in the disconnected additive closure for GReps of an object finite pre-additive category.
#! It returns a list of tuples of the format $[ [ m_i, S_i ], \dots, [ m_j, S_j ] ]$
#! representing a direct sum $S_i^{m_i} \oplus \dots \oplus S_j^{m_j}$ where
#! * $S_i, \dots, S_j$ are objects in the underlying category;
#! * $m_i, ..., m_j$ are integers representing the multiplicties.
#! @Arguments object
#! @Returns A list of tuples consisting of an integer and an object
DeclareAttribute( "MultiplicitiesAndObjects", IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps );

CapJitAddTypeSignature( "MultiplicitiesAndObjects", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
  function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                   IsBigInt,
                   CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) ) );
    
end );

#! @Description
#! The argument is an object in the disconnected additive closure for GReps of an object finite pre-additive category.
#! It returns all underlying objects whose multiplicity is at least once.
#! @Arguments object
#! @Returns 
DeclareAttribute( "Support", IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps );

CapJitAddTypeSignature( "Support", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
  function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) ) );
    
end );

#! @Description
#!  The argument is a morphism in the disconnected additive closure for GReps of an object finite pre-additive category.
#!  It returns a list of matrices of morphisms of the underlying category.
#! @Arguments morphism
#! @Returns A list of matrices of morphisms of the underlying category.
DeclareAttribute( "ListOfMatrices", IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps );

CapJitAddTypeSignature( "ListOfMatrices", [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
 function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) ) );
    
end );

#! @Description
#!  Return the category $A$ underlying the disconnected additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps(</C> $A$ <C>)</C>.
#! @Arguments DAC
DeclareAttribute( "UnderlyingCategory", IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps );

CapJitAddTypeSignature( "UnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of objects in the category $A$ underlying the disconnected additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps(</C> $A$ <C>)</C>.
#! @Arguments DUC
DeclareAttribute( "NumberOfObjectsOfUnderlyingCategory", IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps );

CapJitAddTypeSignature( "NumberOfObjectsOfUnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
  function ( input_types )
    
    return IsBigInt;
    
end );

#! @Description
#! The argument is an object $O$ in a disconnected additive closure for GReps $C^\oplus$ of an object finite pre-additive category $C$.
#! It returns a list of objects of $C$ in the format
#! $[ \underbrace{S_1, \dots, S_1}_{i_1}, \dots, \underbrace{S_n, \dots, S_n}_{i_n} ]$
#! corresponding to the list of multiplicties $[ [ m_i, S_i ], \dots, [ m_j, S_j ] ]$ of $A$.
#! @Arguments A
#! @Returns A list of objects of the underlying category.
DeclareAttribute( "UnderlyingObjectList", IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps );

CapJitAddTypeSignature( "UnderlyingObjectList", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ],
  function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf( CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) ) );
    
end );

####################################
##
#! @Section Operators
##
####################################

#! @Description
#! The argument is a morphism $M$ in the disconnected additive closure for GReps of an object finite pre-additive category
#! <A>AC</A><C> := AdditiveClosureOfObjectFiniteDisconnectedCategoryGReps(</C> $A$ <C>)</C>
#! and an object $S$ in the underlying category $A$.
#! It returns the matrix corresponding to $S$ in the list of matrices of $M$.
#! @Arguments morphism, object
#! @Returns A matrix of morphisms of the underlying category.
DeclareOperation( "Component",
                  [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
                    IsCapCategoryObject ] );

CapJitAddTypeSignature( "Component",
                        [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps,
                          IsCapCategoryObject ],
 function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) and
               UnderlyingCategory( input_types[1].category ) = input_types[2].category );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) );
    
end );

#! @Description
#! The arguments are an object $O$ in a disconnected additive closure $C^\oplus$ of an object finite category $C$
#! and an integer $i$.
#! The output is the $i$'th entry in <C>UnderlyingObjectList</C>($A$).
#! @Arguments A, i
#! @Returns an object in $C$
DeclareOperation( "[]", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsObjectInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsInt ], function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) );
    
    return CapJitDataTypeOfObjectOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#! The arguments are a morphism $\alpha \colon A \to B$ in a disconnected additive closure $C^\oplus$  of an object finite
#! pre-additive category $C$ and two integers $i,j$.
#! The output is the $i$'th morphism matrix in <C>ListOfMatrices</C>($\alpha$), i.e.,
#! the morphism matrix for the $i$'th object of the underlying category.
#! @Arguments alpha, i, j
#! @Returns a morphism $C$
DeclareOperation( "[]", [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsInt ] );

CapJitAddTypeSignature( "[]", [ IsMorphismInAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps, IsInt ], function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#! The input is either
#! * a list of objects or
#! * a list of matrices of morphisms
#! in the underlying category.
#! This operation then constructs either an object or a morphism in <C>AdditiveClosureOfObjectFiniteDisconnectedCategory</C>.
#! For a list of objects, the list will be automatically sorted and the underlying
#! order on the objects need not be respected.
#! 
#! WARNING: Morphism matrices of dimensions $0 \times n$ for $n \geq 1$ are not supported.
#! @Arguments list, DAC
DeclareOperation( "/", [ IsList, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ] );

#! @Description
#! This is a convenience method for
#! <C>ObjectConstructor</C> and <C>MorphismConstructor</C>.
#! @Arguments object or morphism, DAC
#! @Returns an object or morphism in DAC.
DeclareOperation( "/", [ IsCapCategoryCell, IsAdditiveClosureOfObjectFiniteDisconnectedCategoryGReps ] );

