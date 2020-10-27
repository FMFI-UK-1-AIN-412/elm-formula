module Formula.Signed exposing
    ( Signed(..)
    , toString
    , isAlpha, isBeta, isGamma, isDelta, isComplementary, isSubformulaOf, getFormula, subformulas
    )

{-| This library exports signed formulas.


# Definitions

@docs Signed


# Strings

@docs toString


# Tableau helpers

@docs isAlpha, isBeta, isGamma, isDelta, isComplementary, isSubformulaOf, getFormula, subformulas

-}

import Formula exposing (Formula(..))


{-| Signed with T[rue] or F[alse]
-}
type Signed a
    = T a
    | F a


type Type
    = Alpha
    | Beta
    | Gamma
    | Delta


negType : Type -> Type
negType t =
    case t of
        Alpha ->
            Beta

        Beta ->
            Alpha

        Gamma ->
            Delta

        Delta ->
            Gamma


neg : Signed Formula -> Signed Formula
neg sf =
    case sf of
        T f ->
            F f

        F f ->
            T f


getType : Signed Formula -> Type
getType sf =
    case sf of
        T FF ->
            Alpha

        T FT ->
            Alpha

        T (Atom _ _) ->
            Alpha

        F (Atom _ _) ->
            Alpha

        T (Neg _) ->
            Alpha

        F (Neg _) ->
            Alpha

        T (Conj _ _) ->
            Alpha

        T (Disj _ _) ->
            Beta

        T (Impl _ _) ->
            Beta

        T (ForAll _ _) ->
            Gamma

        T (Exists _ _) ->
            Delta

        T (Eq _ _) ->
            Alpha

        F (Eq _ _) ->
            Alpha

        F f ->
            negType <| getType <| T f


{-| Is the signed formula of type Alpha
-}
isAlpha : Signed Formula -> Bool
isAlpha x =
    Alpha == getType x


{-| Is the signed formula of type Beta
-}
isBeta : Signed Formula -> Bool
isBeta x =
    Beta == getType x


{-| Is the signed formula of type Gamma
-}
isGamma : Signed Formula -> Bool
isGamma x =
    Gamma == getType x


{-| Is the signed formula of type Delta
-}
isDelta : Signed Formula -> Bool
isDelta x =
    Delta == getType x


{-| Get signed subformulas as a list of signed formulas
-}
subformulas : Signed Formula -> List (Signed Formula)
subformulas sf =
    case sf of
        T (Neg f) ->
            [ F f ]

        T (Conj l r) ->
            [ T l, T r ]

        T (Disj l r) ->
            [ T l, T r ]

        T (Impl l r) ->
            [ F l, T r ]

        T (ForAll _ f) ->
            [ T f ]

        T (Exists _ f) ->
            [ T f ]

        T _ ->
            []

        F f ->
            T f |> subformulas |> List.map neg


{-| Is the first a Signed subformula of the second
-}
isSubformulaOf : Signed Formula -> Signed Formula -> Bool
isSubformulaOf a b =
    List.member a (subformulas b)


{-| Is the first Signed Formula complementary of the second Signed Formula
-}
isComplementary : Signed Formula -> Signed Formula -> Bool
isComplementary a b =
    case ( a, b ) of
        ( T x, F y ) ->
            x == y

        ( F x, T y ) ->
            x == y

        _ ->
            False


{-| Get Formula out of Signed Formula
-}
getFormula : Signed Formula -> Formula
getFormula sf =
    case sf of
        T f ->
            f

        F f ->
            f


{-| String representation of a Signed Formula
-}
toString : Signed Formula -> String
toString sf =
    case sf of
        T f ->
            "T " ++ Formula.toString f

        F f ->
            "F " ++ Formula.toString f
