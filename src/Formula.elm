module Formula
    exposing
        ( Formula(..)
        , Signed(..)
        , Substitution
        , Term(..)
        , errorString
        , freeFormula
        , isAlpha
        , isBeta
        , isDelta
        , isGamma
        , isSignedComplementary
        , isSignedSubformulaOf
        , isSubformulaOf
        , parse
        , parseSigned
        , parseTerm
        , removeQuantifierAndSubstitute
        , signedGetFormula
        , signedSubformulas
        , strFormula
        , strSigned
        , strSubstitution
        , strTerm
        , substitute
        )

{-| This library parses and exports formulas.


# Definitions

@docs Formula, Signed, Substitution, Term


# Parsers

@docs parse, parseSigned, parseTerm


# Strings

@docs strFormula, strSigned, strTerm, strSubstitution, errorString


# Helpers

@docs substitute, isAlpha, isBeta, isGamma, isDelta, freeFormula, removeQuantifierAndSubstitute, isSignedComplementary, isSignedSubformulaOf, signedGetFormula, signedSubformulas, isSubformulaOf

-}

import Char
import Dict exposing (Dict)
import Parser
    exposing
        ( (|.)
        , (|=)
        , Parser
        , delayedCommit
        , delayedCommitMap
        , end
        , float
        , ignore
        , inContext
        , keyword
        , lazy
        , oneOf
        , oneOrMore
        , repeat
        , succeed
        , symbol
        , zeroOrMore
        )
import Parser.LanguageKit exposing (sequence, variable, whitespace)
import Result as R
import Set exposing (Set)


{-| Term
-}
type Term
    = Var String
    | Fun String (List Term)


{-| Formula
-}
type Formula
    = Atom String (List Term)
    | Neg Formula
    | Disj Formula Formula
    | Conj Formula Formula
    | Impl Formula Formula
    | ForAll String Formula
    | Exists String Formula
    | FF
    | FT


{-| Type alias for substitution
-}
type alias Substitution =
    Dict String Term


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

        ForAll _ sf ->
            [ sf ]

        Exists _ sf ->
            [ sf ]

        _ ->
            []


{-| Is the first a subformula of the second
-}
isSubformulaOf : Formula -> Formula -> Bool
isSubformulaOf a b =
    List.member a (subformulas b)



--
-- First-order syntactic operations
--


freeTermA : Term -> Set String -> Set String
freeTermA t fvs =
    case t of
        Var x ->
            Set.insert x fvs

        Fun _ ts ->
            List.foldl freeTermA fvs ts


freeTerm : Term -> Set String
freeTerm t =
    freeTermA t Set.empty


{-| Returns set of all free variables in given formula
-}
freeFormula : Formula -> Set String
freeFormula f =
    let
        freeFormulaA : Formula -> Set String -> Set String
        freeFormulaA f fvs =
            case f of
                Atom _ ts ->
                    List.foldl freeTermA fvs ts

                ForAll x sf ->
                    Set.remove x <| freeFormulaA sf fvs

                Exists x sf ->
                    Set.remove x <| freeFormulaA sf fvs

                _ ->
                    List.foldl freeFormulaA fvs <| subformulas f
    in
    freeFormulaA f Set.empty


substTerm : Substitution -> Term -> Term
substTerm sigma t =
    case t of
        Var x ->
            case Dict.get x sigma of
                Just xt ->
                    xt

                Nothing ->
                    t

        Fun f ts ->
            Fun f <| List.map (substTerm sigma) ts


mapResult : (a -> Result x b) -> List a -> Result x (List b)
mapResult f =
    List.foldr (Result.map2 (::) << f) (Ok [])


{-| Removes quantifier from given signed formula and returns formula after substitution or error
-}
removeQuantifierAndSubstitute : Substitution -> Formula -> Result String Formula
removeQuantifierAndSubstitute substitution original =
    if Dict.size substitution > 1 then
        Err "there is more than one substitution pair"
    else
        case original of
            ForAll s f ->
                if List.member s (Dict.keys substitution) then
                    substitute substitution f
                else
                    Err "substituted variable isn't in substitution"

            Exists s f ->
                if List.member s (Dict.keys substitution) then
                    substitute substitution f
                else
                    Err "substituted variable isn't in substitution"

            _ ->
                Err "formula doesn't start with quantifier"


{-| Checks if substitution is applicable and substitutes if yes. Returns Result.
ErrMessage or Formula after substitution
-}
substitute : Substitution -> Formula -> Result String Formula
substitute σ f =
    let
        canSubst : String -> Term -> Set String -> Result String Term
        canSubst x t bound =
            let
                clashing =
                    Set.intersect bound (freeTerm t)

                strVars xs =
                    String.join ", " xs

                varsToBe xs =
                    "variable"
                        ++ (if Set.size xs == 1 then
                                ""
                            else
                                "s"
                           )
                        ++ " "
                        ++ strVars (Set.toList xs)
                        ++ (if Set.size xs == 1 then
                                " is"
                            else
                                " are"
                           )
            in
            if Set.isEmpty clashing then
                Ok t
            else
                Err <|
                    String.join " "
                        [ "Cannot substitute"
                        , strTerm t
                        , "for"
                        , x ++ ";"
                        , varsToBe clashing
                        , "bound"
                        ]

        substT : Substitution -> Set String -> Term -> Result String Term
        substT σ bound t =
            let
                subst t =
                    case t of
                        Var x ->
                            case Dict.get x σ of
                                Just xt ->
                                    canSubst x xt bound

                                Nothing ->
                                    Ok t

                        Fun f ts ->
                            R.map (Fun f) <| substTs σ bound ts
            in
            subst t

        substTs : Substitution -> Set String -> List Term -> Result String (List Term)
        substTs σ bound lst =
            mapResult (substT σ bound) lst

        substF : Substitution -> Set String -> Formula -> Result String Formula
        substF σ bound f =
            let
                subst =
                    substF σ bound
            in
            case f of
                Atom p ts ->
                    R.map (Atom p) (substTs σ bound ts)

                ForAll x sf ->
                    R.map (ForAll x)
                        (substF (Dict.remove x σ) (Set.insert x bound) sf)

                Exists x sf ->
                    R.map (Exists x)
                        (substF (Dict.remove x σ) (Set.insert x bound) sf)

                Disj lf rf ->
                    R.map2 Disj (subst lf) (subst rf)

                Conj lf rf ->
                    R.map2 Conj (subst lf) (subst rf)

                Impl lf rf ->
                    R.map2 Impl (subst lf) (subst rf)

                Neg sf ->
                    R.map Neg (subst sf)

                _ ->
                    Ok f
    in
    substF σ Set.empty f


predicates : Formula -> Set String
predicates f =
    let
        predicatesA f ps =
            case f of
                Atom p _ ->
                    Set.insert p ps

                _ ->
                    List.foldl predicatesA ps <| subformulas f
    in
    predicatesA f Set.empty


functions : Formula -> Set String
functions f =
    let
        functionsTA t fs =
            case t of
                Fun f ts ->
                    Set.insert f <| List.foldl functionsTA fs ts

                _ ->
                    fs

        functionsA f fs =
            case f of
                Atom p ts ->
                    List.foldl functionsTA fs ts

                _ ->
                    List.foldl functionsA fs <| subformulas f
    in
    functionsA f Set.empty


variables : Formula -> Set String
variables f =
    let
        variablesTA : Term -> Set String -> Set String
        variablesTA t vs =
            case t of
                Fun _ ts ->
                    List.foldl variablesTA vs ts

                Var x ->
                    Set.insert x vs

        variablesA : Formula -> Set String -> Set String
        variablesA f vs =
            case f of
                Atom p ts ->
                    List.foldl variablesTA vs ts

                _ ->
                    List.foldl variablesA vs <| subformulas f
    in
    variablesA f Set.empty



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



--
-- Parsing
--


{-| Parse string to Signed Formula
-}
parseSigned : String -> Result Parser.Error (Signed Formula)
parseSigned =
    Parser.run (succeed identity |. spaces |= signedFormula |. spaces |. end)


signedFormula : Parser (Signed Formula)
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


{-| Parses string to Term
-}
parseTerm : String -> Result Parser.Error Term
parseTerm =
    Parser.run (succeed identity |. spaces |= term |. spaces |. end)


{-| Parse string to Formula
-}
parse : String -> Result Parser.Error Formula
parse =
    Parser.run (succeed identity |. spaces |= formula |. spaces |. end)


{-| Format parsing error
-}
errorString : Parser.Error -> String
errorString e =
    "Invalid formula: " ++ toString e


formula : Parser Formula
formula =
    oneOf
        [ succeed Atom
            |= identifier
            |. spaces
            |= oneOf
                [ inContext "predicate arguments" args
                , succeed []
                ]
        , lazy (\_ -> quantified [ "∀", "\\A", "\\forall", "\\a" ] ForAll)

        -- keep \exists before \e
        , lazy (\_ -> quantified [ "∃", "\\E", "\\exists", "\\e" ] Exists)
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


binary : List String -> (Formula -> Formula -> value) -> Parser value
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


quantified : List String -> (String -> Formula -> Formula) -> Parser Formula
quantified symbols constructor =
    succeed constructor
        |. oneOfSymbols symbols
        |. spaces
        |= lazy (\_ -> identifier)
        |. spaces
        |= lazy (\_ -> formula)


args : Parser (List Term)
args =
    succeed (::)
        |. symbol "("
        |. spaces
        |= lazy (\_ -> term)
        |. spaces
        |= lazy (\_ -> repeat zeroOrMore nextArg)
        |. symbol ")"


nextArg : Parser Term
nextArg =
    succeed identity
        |. symbol ","
        |. spaces
        |= term
        |. spaces


term : Parser Term
term =
    identifier
        |> Parser.andThen
            (\name ->
                oneOf
                    [ succeed (\args -> Fun name args)
                        |= lazy (\_ -> inContext "function arguments" args)
                    , succeed (Var name)
                    ]
            )


identifier : Parser String
identifier =
    variable isLetter isIdentChar Set.empty


oneOfSymbols : List String -> Parser ()
oneOfSymbols syms =
    oneOf (List.map symbol syms)


isLetter : Char -> Bool
isLetter char =
    Char.isLower char
        || Char.isUpper char


isIdentChar : Char -> Bool
isIdentChar char =
    isLetter char
        || Char.isDigit char
        || char
        == '_'


spaces : Parser ()
spaces =
    ignore zeroOrMore (\char -> char == ' ')


{-| String representation of a Substitution
-}
strSubstitution : Substitution -> String
strSubstitution s =
    "("
        ++ (s
                |> Dict.toList
                |> List.map (\( v, t ) -> v ++ "->" ++ strTerm t)
                |> String.join ","
           )
        ++ ")"


{-| String representation of a Signed Formula
-}
strSigned : Signed Formula -> String
strSigned sf =
    case sf of
        T f ->
            "T " ++ strFormula f

        F f ->
            "F " ++ strFormula f


{-| String representation of a Formula
-}
strFormula : Formula -> String
strFormula f =
    let
        strBinF lf c rf =
            "(" ++ strFormula lf ++ c ++ strFormula rf ++ ")"

        strQF q bv f =
            q ++ bv ++ atomSpace f ++ strFormula f

        atomSpace f =
            case f of
                Atom _ _ ->
                    " "

                _ ->
                    ""
    in
    case f of
        FT ->
            "True"

        FF ->
            "False"

        Atom p [] ->
            p

        Atom p ts ->
            p ++ strArgs ts

        Neg f ->
            "¬" ++ strFormula f

        Conj lf rf ->
            strBinF lf "∧" rf

        Disj lf rf ->
            strBinF lf "∨" rf

        Impl lf rf ->
            strBinF lf "→" rf

        ForAll bv f ->
            strQF "∀" bv f

        Exists bv f ->
            strQF "∃" bv f


strArgs : List Term -> String
strArgs ts =
    "(" ++ String.join "," (List.map strTerm ts) ++ ")"


{-| String representation of a Term
-}
strTerm : Term -> String
strTerm t =
    case t of
        Var v ->
            v

        Fun f ts ->
            f ++ strArgs ts



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
