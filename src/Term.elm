module Term exposing (Term(..), strTerm, Substitution, strSubstitution, freeTerm, freeTermA,
            substTerm, substTs)


import Set exposing(Set)
import Dict exposing (Dict)
import Result as R


{-| Type alias for term
-}
type Term
    = Var String
    | Fun String (List Term)


{-| Type alias for substitution
-}
type alias Substitution =
    Dict String Term


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


substT : Substitution -> Set String -> Term -> Result String Term
substT σ bound tt =
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
    subst tt


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


substTs : Substitution -> Set String -> List Term -> Result String (List Term)
substTs σ bound lst =
    mapResult (substT σ bound) lst


mapResult : (a -> Result x b) -> List a -> Result x (List b)
mapResult f =
    List.foldr (Result.map2 (::) << f) (Ok [])


{-| String representation of a Term
-}
strTerm : Term -> String
strTerm t =
    case t of
        Var v ->
            v

        Fun f ts ->
            f ++ strArgs ts

strArgs : List Term -> String
strArgs ts =
    "(" ++ String.join "," (List.map strTerm ts) ++ ")"


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