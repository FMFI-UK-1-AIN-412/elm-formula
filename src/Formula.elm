module Formula exposing
    ( Formula(..),  strFormula, 
    substitute,  freeFormula, removeQuantifierAndSubstitute, isSubformulaOf)

{-| This library exports and parses formulas.


# Definitions

@docs Formula, Signed, Substitution, Term


# Parsers

@docs parse, parseSigned, parseTerm


# Strings

@docs strFormula, strSigned, strTerm, strSubstitution, errorString


# Tableau helpers

@docs substitute, isAlpha, isBeta, isGamma, isDelta, freeFormula, removeQuantifierAndSubstitute, isSignedComplementary, isSignedSubformulaOf, signedGetFormula, signedSubformulas, isSubformulaOf

-}

import Term exposing(Term(..), Substitution, freeTermA, substTs, strArgs) 
import Char
import Dict exposing (Dict)
import Result as R
import Set exposing (Set)


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


{-| Returns set of all free variables in given formula
-}
freeFormula : Formula -> Set String
freeFormula f =
    freeFormulaA f Set.empty




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


{-| Checks if substitution is applicable and substitutes if yes. Returns Result.
ErrMessage or Formula after substitution
-}
substitute : Substitution -> Formula -> Result String Formula
substitute σ f =
    substF σ Set.empty f


predicatesA f ps =
    case f of
        Atom p _ ->
            Set.insert p ps

        _ ->
            List.foldl predicatesA ps <| subformulas f


predicates : Formula -> Set String
predicates f =
    predicatesA f Set.empty


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


functions : Formula -> Set String
functions f =
    functionsA f Set.empty


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


variables : Formula -> Set String
variables f =
    variablesA f Set.empty



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


{-| String representation of a Formula
-}
strFormula : Formula -> String
strFormula f =
    case f of
        FT ->
            "True"

        FF ->
            "False"

        Atom p [] ->
            p

        Atom p ts ->
            p ++ strArgs ts

        Neg sf ->
            "¬" ++ strFormula sf

        Conj lf rf ->
            strBinF lf "∧" rf

        Disj lf rf ->
            strBinF lf "∨" rf

        Impl lf rf ->
            strBinF lf "→" rf

        ForAll bv sf ->
            strQF "∀" bv sf

        Exists bv sf ->
            strQF "∃" bv sf



{- vim: set sw=2 ts=2 sts=2 et : -}
