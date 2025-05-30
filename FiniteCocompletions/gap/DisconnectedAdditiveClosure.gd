# SPDX-License-Identifier: GPL-2.0-or-later
# FreydCategoriesForCAP: Freyd categories - Formal (co)kernels for additive categories
#
# Declarations
#
#! @Chapter Disconnected additive closure

#! @BeginChunk DisconnectedAddClosureIntroduction

#! Let $C$ be an Ab-category with finitely many objects.
#! The objects of the disconnected additive closure are the same as those of
#! <C>AdditiveClosureOfObjectFiniteCategory</C>, see
#! Chapter <Ref Chap="Chapter_AdditiveClosureObjectFinite" />.
#! 
#! Recall, that the morphisms in the (general) additive closure $C^\oplus$ are given by
#! matrices whose entries are morphisms in $C$ and whose dimensions are given
#! by the number of objects in the source and range lists.
#! 
#! Assume, that for any two non-isomorphic objects $s_1, s_2 \in C$ we have
#! $\mathrm{Hom}_C( s_1, s_2 ) = \{ 0_{ s_1, s_2 } \}$,
#! i.e., the only morphism between $s_1$ and $s_2$ is the zero morphism.
#! Then, after reordering the rows and columns of the matrix of morphisms as in
#! Chapter <Ref Chap="Chapter_AdditiveClosureObjectFinite" /> and removing the
#! zero rows and columns, we get a block-diagonal matrix.
#! So we only need to remember the blocks on the diagonal.
#! 
#! For example, assume all the objects of $C$ are $\{ s_1, s_2, s_3, s_4 \}$ satisfying
#! $\mathrm{Hom}_C(s_i,s_j) = \{ 0_{ij} \}$ for $i \neq j$.
#! A morphism
#! @BeginLatexOnly
#! \begin{center}
#!      $s_1 \oplus s_2 \oplus s_1 \oplus s_3 \rightarrow s_3 \oplus s_1 \oplus s_3$
#! \end{center}
#! @EndLatexOnly
#! in $C^\oplus$ is given by the below left matrix.
#! This will be reordered into the below middle matrix (via <C>AdditiveClosureOfObjectFiniteCategory</C>)
#! for the corresponding morphism
#! @BeginLatexOnly
#! \begin{center}
#!      $[ 4, [ 2, 1, 1, 0 ] ] \rightarrow [ 3, [ 1, 0, 2, 0 ] ]$.
#! \end{center}
#! @EndLatexOnly
#! The disconnected additive closure then extracts the blocks into the below right
#! list of matrices.
#! @BeginLatexOnly
#! \begin{center}
#!      \begin{array}{c|ccc}
#!                 & s_3    & s_1    & s_3    \\
#!          \hline
#!          s_1    & 0_{13} & m_{11} & 0_{13} \\
#!          s_2    & 0_{23} & 0_{21} & 0_{23} \\
#!          s_1    & 0_{13} & m_{11} & 0_{13} \\
#!          s_3    & m_{33} & 0_{31} & m_{33}
#!      \end{array}
#!      \qquad
#!      \begin{array}{c|ccc}
#!                 & s_1    & s_3    & s_3    \\
#!          \hline
#!          s_1    & \cellcolor{lightgray!25} m_{11} & 0_{13} & 0_{13} \\
#!          s_1    & \cellcolor{lightgray!25} m_{11} & 0_{13} & 0_{13} \\
#!          \textcolor{lightgray}{s_2} & \textcolor{lightgray}{0_{21}} & \textcolor{lightgray}{0_{23}} & \textcolor{lightgray}{0_{23}} \\
#!          s_3    & 0_{31} & \cellcolor{lightgray!25} m_{33} & \cellcolor{lightgray!25} m_{33}
#!      \end{array}
#!      \qquad
#!      \Biggl[
#!          \begin{pmatrix}
#!              m_{11} \\
#!              m_{11}
#!          \end{pmatrix},
#!          \;
#!          \begin{pmatrix}{}
#!          \end{pmatrix},
#!          \;
#!          \begin{pmatrix}
#!              m_{33} & m_{33}
#!          \end{pmatrix}
#!          \;
#!          \begin{pmatrix}{}
#!          \end{pmatrix},
#!      \Biggr]
#! \end{center}
#! @EndLatexOnly
#! The first zero matrix has dimensions $1 \times 0$ and
#! the second zero matrix has dimensions $0 \times 0$.
#! 
#! If $C$ is skeletal, then the disconnected additive closure is also skeletal.

#! @EndChunk

####################################
##
#! @Section GAP Categories
##
####################################

#! @Description
#!  The GAP category of discrete additive closures of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsDisconnectedAdditiveClosure",
                 IsCapCategory );

#! @Description
#!  The GAP category of objects in discrete additive closures of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsObjectInDisconnectedAdditiveClosure",
                 IsCapCategoryObject );

#! @Description
#!  The GAP category of morphisms in discrete additive closures of object finite Ab-categories.
#! @Arguments object
#! @Returns true or false
DeclareCategory( "IsMorphismInDisconnectedAdditiveClosure",
                 IsCapCategoryMorphism );

####################################
##
#! @Section Constructors
##
####################################

#! @Description
#!  The argument is an object finite Ab-category $C$. The output is its discrete additive closure $C^\oplus$.
#! @Arguments C
#! @Returns the category $C^{\oplus}$
DeclareAttribute( "DisconnectedAdditiveClosure",
                  IsCapCategory );

#! @Description
#!  Same as <Ref Attr="DisconnectedAdditiveClosure" Label="for IsCapCategory" />, but as an operation instead of an attribute.
#! @Arguments C
#! @Returns the category $C^\oplus$
DeclareOperation( "DISCONNECTED_ADDITIVE_CLOSURE",
                  [ IsCapCategory ] );

if false then
#! @Description
#! The input is a discrete additive closure <A>AC</A><C> := DisconnectedAdditiveClosure(</C> $A$ <C>)</C>
#! of an object finite Ab-category <A>A</A> and a list of the format
#! $[ i, [ i_1, ..., i_n ] ]$ representing a direct sum $A_1^{i_1} \oplus \dots \oplus A_n^{i_n}$ where
#! * $A_1, \dots, A_n$ are all of the objects in the underlying category;
#! * $i_1, ..., i_n$ are integers representing the multiplicties;
#! * $i$ is the sum of integers $i_1 + \dots + i_n$.
#! See also <Ref Attr="ChecksumAndMultiplicities" Label="for IsObjectInDisconnectedAdditiveClosure" />.
#! @Arguments AC, l
#! @Returns a &CAP; category object
DeclareOperation( "ObjectConstructor", [ IsObjectInDisconnectedAdditiveClosure, IsList ] );

#! @Description
#! The input is a discrete additive closure <A>AC</A><C> := DisconnectedAdditiveClosure(</C> $A$ <C>)</C>
#! of an object finite Ab-category <A>A</A>,
#! * <A>s</A> is the source object,
#! * <A>list_of_matrices</A> is a list of lists of lists of morphisms in A,
#! * <A>t</A> is the target object.
#! See also <Ref Attr="ListOfMatrices" Label="for IsMorphismInDisconnectedAdditiveClosure" />.
#! @Arguments AC, s, list_of_matrices, t
#! @Returns a &CAP; category morphism
DeclareOperation( "MorphismConstructor", [ IsMorphismInDisconnectedAdditiveClosure, IsList ] );
fi;

####################################
#
#! @Section Attributes
#
####################################

#! @Description
#!  The argument is an object in the discrete additive closure of an object finite Ab-category.
#!  It returns a list of the format $[ i, [ i_1, ..., i_n ] ]$ representing a
#!  direct sum $A_1^{i_1} \oplus \dots \oplus A_n^{i_n}$ where
#!  * $A_1, \dots, A_n$ are all of the objects in the underlying category;
#!  * $i_1, \dots, i_n$ are integers representing the multiplicties;
#!  * i is the sum of integers $i_1 + \dots + i_n$.
#! @Arguments object
#! @Returns A list consisting of an integer and a list of integers.
DeclareAttribute( "ChecksumAndMultiplicities",
        IsObjectInDisconnectedAdditiveClosure );

CapJitAddTypeSignature( "ChecksumAndMultiplicities", [ IsObjectInDisconnectedAdditiveClosure ],
 function ( input_types )
    
    Assert( 0, IsDisconnectedAdditiveClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfNTupleOf( 2,
                   IsBigInt,
                   CapJitDataTypeOfListOf( IsBigInt ) );
    
end );

#! @Description
#!  The argument is a morphism in the additive closure of an object finite Ab-category.
#!  It returns a list of matrices of morphisms of the underlying category.
#! @Arguments morphism
#! @Returns A list of matrices of morphisms of the underlying category.
DeclareAttribute( "ListOfMatrices",
        IsMorphismInDisconnectedAdditiveClosure );

CapJitAddTypeSignature( "ListOfMatrices", [ IsMorphismInDisconnectedAdditiveClosure ],
 function ( input_types )
    
    Assert( 0, IsDisconnectedAdditiveClosure( input_types[1].category ) );
    
    return CapJitDataTypeOfListOf(
                CapJitDataTypeOfListOf(
                    CapJitDataTypeOfListOf(
                        CapJitDataTypeOfMorphismOfCategory( UnderlyingCategory( input_types[1].category ) ) ) ) );
        
end );

#! @Description
#!  Return the category $A$ underlying the additive closure
#!  <A>AC</A><C> := DisconnectedAdditiveClosure(</C> $A$ <C>)</C>.
#! @Arguments DAC
DeclareAttribute( "UnderlyingCategory",
        IsDisconnectedAdditiveClosure );

CapJitAddTypeSignature( "UnderlyingCategory", [ IsDisconnectedAdditiveClosure ],
  function ( input_types )
    
    return CapJitDataTypeOfCategory( UnderlyingCategory( input_types[1].category ) );
    
end );

#! @Description
#!  Return the number of objects in the category $A$ underlying the discrete additive closure
#!  <A>AC</A><C> := DisconnectedAdditiveClosure(</C> $A$ <C>)</C>.
#! @Arguments DUC
DeclareAttribute( "NumberOfObjectsOfUnderlyingCategory",
        IsDisconnectedAdditiveClosure );

CapJitAddTypeSignature( "NumberOfObjectsOfUnderlyingCategory", [ IsDisconnectedAdditiveClosure ],
  function ( input_types )
    
    return IsBigInt;
    
end );
