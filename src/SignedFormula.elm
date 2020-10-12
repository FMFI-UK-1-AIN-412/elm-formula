module SignedFormula exposing (Signed(..), strSigned, isAlpha, isBeta, isGamma, isDelta, 
    isSignedComplementary, isSignedSubformulaOf, signedGetFormula, signedSubformulas)

import Formula exposing(Formula(..), strFormula)


{-| Signed with T[rue] or F[alse]
-}
type Signed a
    = T a
    | F a


type SignedType
    = Alpha
    | Beta
    | Gamma
    | Delta


negType : SignedType -> SignedType
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


negSigned : Signed Formula -> Signed Formula
negSigned sf =
    case sf of
        T f ->
            F f

        F f ->
            T f


signedType : Signed Formula -> SignedType
signedType sf =
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

        F f ->
            negType <| signedType <| T f


{-| Is the signed formula of type Alpha
-}
isAlpha : Signed Formula -> Bool
isAlpha x =
    Alpha == signedType x


{-| Is the signed formula of type Beta
-}
isBeta : Signed Formula -> Bool
isBeta x =
    Beta == signedType x


{-| Is the signed formula of type Gamma
-}
isGamma : Signed Formula -> Bool
isGamma x =
    Gamma == signedType x


{-| Is the signed formula of type Delta
-}
isDelta : Signed Formula -> Bool
isDelta x =
    Delta == signedType x


{-| Get signed subformulas as a list of signed formulas
-}
signedSubformulas : Signed Formula -> List (Signed Formula)
signedSubformulas sf =
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
            T f |> signedSubformulas |> List.map negSigned


{-| Is the first a Signed subformula of the second
-}
isSignedSubformulaOf : Signed Formula -> Signed Formula -> Bool
isSignedSubformulaOf a b =
    List.member a (signedSubformulas b)


{-| Is the first Signed Formula complementary of the second Signed Formula
-}
isSignedComplementary : Signed Formula -> Signed Formula -> Bool
isSignedComplementary a b =
    case ( a, b ) of
        ( T x, F y ) ->
            x == y

        ( F x, T y ) ->
            x == y

        _ ->
            False


{-| Get Formula out of Signed Formula
-}
signedGetFormula : Signed Formula -> Formula
signedGetFormula sf =
    case sf of
        T f ->
            f

        F f ->
            f


{-| String representation of a Signed Formula
-}
strSigned : Signed Formula -> String
strSigned sf =
    case sf of
        T f ->
            "T " ++ strFormula f

        F f ->
            "F " ++ strFormula f