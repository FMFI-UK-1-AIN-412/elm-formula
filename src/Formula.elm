module Formula exposing
    ( Formula(..), toString, substitute, free, removeQuantifierAndSubstitute
    , isSubformulaOf)

{-| This library exports formulas.


# Definitions

@docs Formula


# Strings

@docs toString


# Tableau helpers

@docs substitute,  free, removeQuantifierAndSubstitute, isSubformulaOf

-}

import Term exposing(Term(..), Substitution) 
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

freeA : Formula -> Set String -> Set String
freeA f fvs =
    case f of
        Atom _ ts ->
            List.foldl Term.freeA fvs ts

        ForAll x sf ->
            Set.remove x <| freeA sf fvs

        Exists x sf ->
            Set.remove x <| freeA sf fvs

        _ ->
            List.foldl freeA fvs <| subformulas f


{-| Returns set of all free variables in given formula
-}
free : Formula -> Set String
free f =
    freeA f Set.empty




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




subst : Substitution -> Set String -> Formula -> Result String Formula
subst σ bound f =
    let
        substA =
            subst σ bound
    in
    case f of
        Atom p ts ->
            R.map (Atom p) (Term.substs σ bound ts)

        ForAll x sf ->
            R.map (ForAll x)
                (subst (Dict.remove x σ) (Set.insert x bound) sf)

        Exists x sf ->
            R.map (Exists x)
                (subst (Dict.remove x σ) (Set.insert x bound) sf)

        Disj lf rf ->
            R.map2 Disj (substA lf) (substA rf)

        Conj lf rf ->
            R.map2 Conj (substA lf) (substA rf)

        Impl lf rf ->
            R.map2 Impl (substA lf) (substA rf)

        Neg sf ->
            R.map Neg (substA sf)

        _ ->
            Ok f


{-| Checks if substitution is applicable and substitutes if yes. Returns Result.
ErrMessage or Formula after substitution
-}
substitute : Substitution -> Formula -> Result String Formula
substitute σ f =
    subst σ Set.empty f


predicatesA f ps =
    case f of
        Atom p _ ->
            Set.insert p ps

        _ ->
            List.foldl predicatesA ps <| subformulas f


predicates : Formula -> Set String
predicates f =
    predicatesA f Set.empty


functionsA f fs =
    case f of
        Atom p ts ->
            List.foldl Term.functionsA fs ts

        _ ->
            List.foldl functionsA fs <| subformulas f


functions : Formula -> Set String
functions f =
    functionsA f Set.empty


variablesA : Formula -> Set String -> Set String
variablesA f vs =
    case f of
        Atom p ts ->
            List.foldl Term.variablesA vs ts

        _ ->
            List.foldl variablesA vs <| subformulas f


variables : Formula -> Set String
variables f =
    variablesA f Set.empty



strBinF lf c rf =
    "(" ++ toString lf ++ c ++ toString rf ++ ")"


strQF q bv f =
    q ++ bv ++ atomSpace f ++ toString f


atomSpace f =
    case f of
        Atom _ _ ->
            " "

        _ ->
            ""


{-| String representation of a Formula
-}
toString : Formula -> String
toString f =
    case f of
        FT ->
            "True"

        FF ->
            "False"

        Atom p [] ->
            p

        Atom p ts ->
            p ++ Term.strArgs ts

        Neg sf ->
            "¬" ++ toString sf

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
