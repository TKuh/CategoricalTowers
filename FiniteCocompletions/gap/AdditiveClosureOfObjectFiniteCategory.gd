# SPDX-License-Identifier: GPL-2.0-or-later
# FreydCategoriesForCAP: Freyd categories - Formal (co)kernels for additive categories
#
# Declarations
#
#! @Chapter Additive closure of an object finite category

#! @BeginChunk AddClosureIntroduction

#! Let $C$ be an Ab-category and $C^\oplus$ be its additive closure.
#! An object $o =  c_1 \oplus \dots \oplus c_i$ of $C^\oplus$ is modeled as a list
#! of objects $[ c_1, \dots, c_i ]$ with $o_i \in C$. If $C$ has only finitely
#! many objects $\{ c_1, \dots, c_n \}$, a shorter data structure for the objects of $C^\oplus$
#! can be achieved by only remembering the number of occurences of each $c_j$ in the object list of $o$.
#! 
#! For example: assume $C$ contains exactly four objects $\{ c_1, c_2, c_3, c_4 \}$ and let
#! @BeginLatexOnly
#! \begin{center}
#!      o \coloneqq c_2 \oplus c_3 \oplus c_1 \oplus c_3 \oplus c_2 \oplus c_2 \in C^\oplus
#! \end{center}
#! \vspace{-1.5em}
#! @EndLatexOnly
#! be modeled by the list $[ c_2, c_3, c_1, c_3, c_2, c_2 ]$.
#! We can abbreviate this by remembering only the list of multiplicities $[ 1, 3, 2, 0 ]$.
#! Here, the object $c_1$ occurs one time, $c_2$ occurs three times, $c_3$ occurs two times
#! and $c_4$ occurs zero times in $o$.
#! Additionally, we also remember the sum of all multiplicites, which is 6. The final
#! result will hence be $o = [ 6, [ 1, 3, 2, 0 ] ]$. Notice, that this requires the set of
#! objects of $C$ to be ordered.
#! 
#! The morphisms in $C^\oplus$ are given by matrices whose entries are morphisms
#! in $C$ and whose dimensions are given by the number of objects in the source and
#! range lists. In the case that $C$ has only finitely many objects,
#! the morphisms are also given by such matrices except for a reordering of the entries
#! which is required due to the ordering of the list of multiplicities of the source and target.
#! 
#! For example, a morphism $c_1 \oplus c_2 \oplus c_1 \rightarrow c_3 \oplus c_2$
#! is given by the below left matrix and when $C$ has only finitely many objects,
#! this is rearranged into the below right matrix for the corresponding morphism
#! $[ 3, [ 2, 1, 0, 0 ] ] \rightarrow [ 2, [ 0, 1, 1, 0 ] ]$.
#! 
#! @BeginLatexOnly
#! \begin{center}
#!      \begin{array}{c|cc}
#!              & c_3    & c_2 \\
#!          \hline
#!          c_1 & m_{13} & m_{12} \\
#!          c_2 & m_{23} & m_{22} \\
#!          c_1 & m_{13} & m_{12}
#!      \end{array}
#!      \qquad \qquad
#!      \begin{array}{c|cc}
#!              & c_2    & c_3 \\
#!          \hline
#!          c_1 & m_{12} & m_{13} \\
#!          c_1 & m_{12} & m_{13} \\
#!          c_2 & m_{22} & m_{23}
#!      \end{array}
#! \end{center}
#! @EndLatexOnly
#!
#! If $C$ is additionally skeletal, then this additive closure is also skeletal.

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The GAP category of additive closures of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsAdditiveClosureOfObjectFiniteCategory",
                 IsCapCategory );

#! @Description
#!  The GAP category of objects in additive closures of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInAdditiveClosureOfObjectFiniteCategory",
                 IsCapCategoryObject );

#! @Description
#!  The GAP category of morphisms in additive closures of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInAdditiveClosureOfObjectFiniteCategory",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  The argument is an object finite Ab-category $C$. The output is its additive closure $C^\oplus$.
#! @Arguments C
#! @Returns the category $C^\oplus$
DeclareAttribute( "AdditiveClosureOfObjectFiniteCategory",
                  IsCapCategory );

#! @Description
#!  Same as <Ref Attr="AdditiveClosureOfObjectFiniteCategory" Label="for IsCapCategory" />, but as an operation instead of an attribute.
#! @Arguments C
#! @Returns the category $C^\oplus$
DeclareOperation( "ADDITIVE_CLOSURE_Of_OBJECT_FINITE_CATEGORY",
                  [ IsCapCategory ] );

if false then
#! @Description
#! The input is an additive closure <A>AC</A><C> := AdditiveClosureOfObjectFiniteCategory(</C> $A$ <C>)</C>
#! of an object finite Ab-category <A>A</A> and a list of the format
#! $[ i, [ i_1, ..., i_n ] ]$ representing a direct sum $A_1^{i_1} \oplus \dots \oplus A_n^{i_n}$ where
#! * $A_1, \dots, A_n$ are all of the objects in the underlying category;
#! * $i_1, ..., i_n$ are integers representing the multiplicties;
#! * $i$ is the sum of integers $i_1 + \dots + i_n$.
#! See also <Ref Attr="ChecksumAndMultiplicities" Label="for IsObjectInAdditiveClosureOfObjectFiniteCategory" />.
#! @Arguments AC, l
#! @Returns a &CAP; category object
DeclareOperation( "ObjectConstructor", [ IsAdditiveClosureOfObjectFiniteCategory, IsList ] );

#! @Description
#! The input is an additive closure <A>AC</A><C> := AdditiveClosureOfObjectFiniteCategory(</C> $A$ <C>)</C>
#! of an object finite Ab-category <A>A</A>,
#! * <A>s</A> is the source object,
#! * <A>matrix</A> is a list of lists of morphisms in A,
#! * <A>t</A> is the target object.
#! See also <Ref Attr="MorphismMatrix" Label="for IsMorphismInAdditiveClosureOfObjectFiniteCategory" />.
#! @Arguments AC, s, matrix, t
#! @Returns a &CAP; category morphism
DeclareOperation( "MorphismConstructor", [ IsAdditiveClosureOfObjectFiniteCategory, ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The argument is an object in the additive closure of an object finite Ab-category.
#!  It returns a list of the format $[ i, [ i_1, ..., i_n ] ]$ representing a direct sum $A_1^{i_1} \oplus \dots \oplus A_n^{i_n}$ where
#!  * $A_1, \dots, A_n$ are all of the objects in the underlying category;
#!  * $i_1, ..., i_n$ are integers representing the multiplicties;
#!  * $i$ is the sum of integers $i_1 + \dots + i_n$.
#! @Arguments object
#! @Returns A list consisting of an integer and a list of integers.
DeclareAttribute( "ChecksumAndMultiplicities",
        IsObjectInAdditiveClosureOfObjectFiniteCategory );

CapJitAddTypeSignature( "ChecksumAndMultiplicities", [ IsObjectInAdditiveClosureOfObjectFiniteCategory ],
 function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                   IsBigInt,
                   CapJitDataTypeOfListOf( IsBigInt ) );
    
end );

#! @Description
#!  The argument is a morphism in the additive closure of an object finite Ab-category.
#!  It returns a list of lists representing a matrix of morphisms of the underlying category.
#! @Arguments morphism
#! @Returns A list of lists of morphisms of the underlying category.
DeclareAttribute( "MorphismMatrix",
        IsMorphismInAdditiveClosureOfObjectFiniteCategory );

CapJitAddTypeSignature( "MorphismMatrix", [ IsMorphismInAdditiveClosureOfObjectFiniteCategory ],
 function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                        CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) );
    
end );

#! @Description
#!  Return the category $A$ underlying the additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteCategory(</C> $A$ <C>)</C>.
#! @Arguments AC
#! @Return a &CAP; category
DeclareAttribute( "UnderlyingCategory",
        IsAdditiveClosureOfObjectFiniteCategory );

CapJitAddTypeSignature( "UnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteCategory ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of objects in the category $A$ underlying the additive closure
#!  <A>AC</A><C> := AdditiveClosureOfObjectFiniteCategory(</C> $A$ <C>)</C>.
#! @Arguments AC
#! @Returns An integer
DeclareAttribute( "NumberOfObjectsOfUnderlyingCategory",
        IsAdditiveClosureOfObjectFiniteCategory );

CapJitAddTypeSignature( "NumberOfObjectsOfUnderlyingCategory", [ IsAdditiveClosureOfObjectFiniteCategory ],
  function ( input_types )
    
    return IsBigInt;
    
end );

####################################
##
#! @Section Operators
##
####################################

#! @Description
#! The arguments are a morphism $\alpha \colon A \to B$ between formal direct sums in
#! an additive closure $C^\oplus$ and two integers $i,j$.
#! The output is the $(i,j)$'th entry in <C>MorphismMatrix</C>($\alpha$).
#! @Arguments alpha, i, j
#! @Returns a &CAP; category morphism in $C$
DeclareOperation( "[,]",
                  [ IsMorphismInAdditiveClosureOfObjectFiniteCategory, IsInt, IsInt ] );

CapJitAddTypeSignature( "[,]", [ IsMorphismInAdditiveClosureOfObjectFiniteCategory, IsInt, IsInt ], function ( input_types )
    
    Assert( 0, IsAdditiveClosureOfObjectFiniteCategory( input_types[1].category ) );
    
    return CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#! The input is either
#! * a list of objects or
#! * a list of lists of morphisms
#! in the underlying category.
#! This operation then constructs either an object or a morphism in <C>AdditiveClosureOfObjectFiniteCategory</C>.
DeclareOperation( "/",
                  [ IsList, IsAdditiveClosureOfObjectFiniteCategory ] );

#! @Description
#! This is a convenience method for
#! <C>ObjectConstructor</C> and <C>MorphismConstructor</C>.
DeclareOperation( "/",
                  [ IsCapCategoryCell, IsAdditiveClosureOfObjectFiniteCategory ] );

