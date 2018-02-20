module Formula
    exposing
        ( Formula(..)
        , Signed(..)
        , isAlpha
        , isBeta
        , signedSubformulas
        , isSignedSubformulaOf
        , isSignedComplementary
        , signedGetFormula
        , parseSigned
        , parse
        , errorString
        , strSigned
        , strFormula
        )

{-| This library parses string to formulas


# Definitions

@docs Formula, Signed


# Parsers

@docs parse, parseSigned


# Strings

@docs strFormula, strSigned, errorString


# Helpers

@docs isAlpha, isBeta, isSignedComplementary, isSignedSubformulaOf, signedGetFormula, signedSubformulas

-}

{- todo: in the future, we may expose
   , SignedType(..)
   , subformulas
   , isSubformulaOf
   , negType
   , negSigned
   , signedType
-}

import Char
import Set
import Parser
    exposing
        ( Parser
        , (|.)
        , (|=)
        , succeed
        , symbol
        , float
        , ignore
        , zeroOrMore
        , oneOf
        , lazy
        , keyword
        , delayedCommitMap
        , end
        , oneOrMore
        )
import Parser.LanguageKit exposing (variable, sequence, whitespace)


{-| Formula can be

  - atomic
  - negation of a formula
  - disjunction, conjuction, implication of two formulas
  - FF and FT

-}
type Formula
    = Atom String
    | Neg Formula
    | Disj Formula Formula
    | Conj Formula Formula
    | Impl Formula Formula
    | FF
    | FT


subformulas : Formula -> List Formula
subformulas f =
    case f of
        Neg sf ->
            [ sf ]

        Disj lf rf ->
            [ lf, rf ]

        Conj lf rf ->
            [ lf, rf ]

        Impl lf rf ->
            [ lf, rf ]

        _ ->
            []


isSubformulaOf : Formula -> Formula -> Bool
isSubformulaOf a b =
    List.member a (subformulas b)



--
-- Signed formulas
--


{-| Signed with T[rue] or F[alse]
-}
type Signed a
    = T a
    | F a


type SignedType
    = Alpha
    | Beta


negType : SignedType -> SignedType
negType t =
    case t of
        Alpha ->
            Beta

        Beta ->
            Alpha


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

        T (Atom _) ->
            Alpha

        F (Atom _) ->
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

        F f ->
            negType <| signedType <| T f


{-| Is the formula of type Alpha
-}
isAlpha : Signed Formula -> Bool
isAlpha x =
    Alpha == signedType x


{-| Is the formula of type Beta
-}
isBeta : Signed Formula -> Bool
isBeta x =
    Beta == signedType x


{-| Get signed subformulas as list of signed formulas
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

        T _ ->
            []

        F f ->
            T f |> signedSubformulas |> List.map negSigned


{-| Is the first signed formula of the other
-}
isSignedSubformulaOf : Signed Formula -> Signed Formula -> Bool
isSignedSubformulaOf a b =
    List.member a (signedSubformulas b)


{-| Are the two signed formulas complementary
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


{-| Get formula out of signed formula
-}
signedGetFormula : Signed Formula -> Formula
signedGetFormula sf =
    case sf of
        T f ->
            f

        F f ->
            f



--
-- Parsing
--


{-| Parse string to Signed Formula
-}
parseSigned : String -> Result Parser.Error (Signed Formula)
parseSigned =
    Parser.run (succeed identity |. spaces |= signedFormula |. spaces |. end)


signedFormula =
    succeed identity
        |. spaces
        |= oneOf
            [ succeed T
                |. keyword "T"
                |. spaces
                |= formula
            , succeed F
                |. keyword "F"
                |. spaces
                |= formula
            ]


{-| Parse string to Formula
-}
parse : String -> Result Parser.Error Formula
parse =
    Parser.run (succeed identity |. spaces |= formula |. spaces |. end)


{-| Return error message from parsing error
-}
errorString : Parser.Error -> String
errorString e =
    "Invalid formula: " ++ (toString e)


formula : Parser Formula
formula =
    oneOf
        [ succeed Atom
            |= variable Char.isLower Char.isLower (Set.fromList [])
        , succeed Neg
            |. oneOfSymbols [ "-", "¬", "~" ]
            |. spaces
            |= lazy (\_ -> formula)
        , lazy (\_ -> binary [ "&", "∧", "/\\" ] Conj)
        , lazy (\_ -> binary [ "|", "∨", "\\/" ] Disj)
        , lazy (\_ -> binary [ "->", "→" ] Impl)
        , succeed identity
            |. symbol "("
            |. spaces
            |= lazy (\_ -> formula)
            |. spaces
            |. symbol ")"
        ]


binary conn constructor =
    delayedCommitMap constructor
        (succeed identity
            |. symbol "("
            |. spaces
            |= lazy (\_ -> formula)
            |. spaces
        )
    <|
        succeed identity
            |. oneOfSymbols conn
            |. spaces
            |= lazy (\_ -> formula)
            |. spaces
            |. symbol ")"


oneOfSymbols syms =
    oneOf (List.map symbol syms)


spaces : Parser ()
spaces =
    ignore zeroOrMore (\char -> char == ' ')


{-| Show representation of a Signed Formula. todo: rewrite with toString instead.
-}
strSigned : Signed Formula -> String
strSigned sf =
    case sf of
        T f ->
            "T " ++ (strFormula f)

        F f ->
            "F " ++ (strFormula f)


{-| Show representation of a Formula. todo: rewrite with toString instead.
-}
strFormula : Formula -> String
strFormula f =
    case f of
        FT ->
            "True"

        FF ->
            "False"

        Atom a ->
            a

        Neg f ->
            "¬" ++ (strFormula f)

        Conj lf rf ->
            "(" ++ (strFormula lf) ++ "∧" ++ (strFormula rf) ++ ")"

        Disj lf rf ->
            "(" ++ (strFormula lf) ++ "∨" ++ (strFormula rf) ++ ")"

        Impl lf rf ->
            "(" ++ (strFormula lf) ++ "→" ++ (strFormula rf) ++ ")"



--
-- helper funcs
--


sf : String -> Signed Formula
sf =
    parseSigned >> Result.withDefault (T FF)


f : String -> Formula
f =
    parse >> Result.withDefault FF



{- vim: set sw=2 ts=2 sts=2 et : -}
