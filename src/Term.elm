module Term exposing
    ( Term(..), Substitution
    , toString, strSubstitution, argsToString
    , substitute, substs, subst
    , free, freeA, functionsA, variablesA
    )

{-| This library exports Terms.


# Definitions

@docs Term, Substitution


# Strings

@docs toString, strSubstitution, argsToString


# Tableau helpers

@docs substitute, substs, subst


# Symbol helpers

@docs free, freeA, functionsA, variablesA

-}

import Dict exposing (Dict)
import Result as R
import Set exposing (Set)


{-| Type alias for term
-}
type Term
    = Var String
    | Fun String (List Term)


{-| Type alias for substitution
-}
type alias Substitution =
    Dict String Term


{-| freeA
-}
freeA : Term -> Set String -> Set String
freeA t fvs =
    case t of
        Var x ->
            Set.insert x fvs

        Fun _ ts ->
            List.foldl freeA fvs ts


{-| free
-}
free : Term -> Set String
free t =
    freeA t Set.empty


{-| substitute
-}
substitute : Substitution -> Term -> Term
substitute sigma t =
    case t of
        Var x ->
            case Dict.get x sigma of
                Just xt ->
                    xt

                Nothing ->
                    t

        Fun f ts ->
            Fun f <| List.map (substitute sigma) ts


{-| subst
-}
subst : Substitution -> Set String -> Term -> Result String Term
subst σ bound tt =
    let
        substA t =
            case t of
                Var x ->
                    case Dict.get x σ of
                        Just xt ->
                            canSubst x xt bound

                        Nothing ->
                            Ok t

                Fun f ts ->
                    R.map (Fun f) <| substs σ bound ts
    in
    substA tt


canSubst : String -> Term -> Set String -> Result String Term
canSubst x t bound =
    let
        clashing =
            Set.intersect bound (free t)

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
                , toString t
                , "for"
                , x ++ ";"
                , varsToBe clashing
                , "bound"
                ]


{-| substs
-}
substs : Substitution -> Set String -> List Term -> Result String (List Term)
substs σ bound lst =
    mapResult (subst σ bound) lst


mapResult : (a -> Result x b) -> List a -> Result x (List b)
mapResult f =
    List.foldr (Result.map2 (::) << f) (Ok [])


{-| functionsA
-}
functionsA : Term -> Set String -> Set String
functionsA t fs =
    case t of
        Fun f ts ->
            Set.insert f <| List.foldl functionsA fs ts

        _ ->
            fs


{-| variablesA
-}
variablesA : Term -> Set String -> Set String
variablesA t vs =
    case t of
        Fun _ ts ->
            List.foldl variablesA vs ts

        Var x ->
            Set.insert x vs


{-| String representation of a Term
-}
toString : Term -> String
toString t =
    case t of
        Var v ->
            v

        Fun f ts ->
            f ++ argsToString ts


{-| String represenation of multiple Terms
-}
argsToString : List Term -> String
argsToString ts =
    "(" ++ String.join ", " (List.map toString ts) ++ ")"


{-| String representation of a Substitution
-}
strSubstitution : Substitution -> String
strSubstitution s =
    "("
        ++ (s
                |> Dict.toList
                |> List.map (\( v, t ) -> v ++ " -> " ++ toString t)
                |> String.join ", "
           )
        ++ ")"
