module Formula.Parser exposing 
    (parse, parseSigned, parseTerm)

{-| This library parses formulas.


# Parsers

@docs parse, parseSigned, parseTerm


# Strings

@docs errorString

-}

import Parser
    exposing
        ( (|.)
        , (|=)
        , Parser
        , Trailing(..)
        , backtrackable
        , chompWhile
        , end
        , float
        , keyword
        , lazy
        , map
        , oneOf
        , sequence
        , succeed
        , symbol
        , variable
        )

import Formula exposing(Formula(..))
import Formula.Signed exposing(Signed(..)) 
import Term exposing(Term(..))
import Set exposing (Set)
import Dict exposing (Dict)

{-| Parse string to Signed Formula
-}
parseSigned : String -> Result (List Parser.DeadEnd) (Signed Formula)
parseSigned =
    Parser.run (succeed identity |. spaces |= signedFormula |. spaces |. end)


{-| Parses string to Term
-}
parseTerm : String -> Result (List Parser.DeadEnd) Term
parseTerm =
    Parser.run (succeed identity |. spaces |= term |. spaces |. end)


{-| Parse string to Formula
-}
parse : String -> Result (List Parser.DeadEnd) Formula
parse =
    Parser.run (succeed identity |. spaces |= formula |. spaces |. end)


{-| Format parsing error
-}
errorString : List Parser.DeadEnd -> String
errorString e =
    "Invalid formula: " ++ Parser.deadEndsToString e


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


formula : Parser Formula
formula =
    oneOf
        [ succeed Atom
            |= identifier
            |. spaces
            |= oneOf
                [ args
                , succeed []
                ]
        , lazy (\_ -> quantified [ "∀", "\\A", "\\forall", "\\a" ] ForAll)

        -- keep \exists before \e
        , lazy (\_ -> quantified [ "∃", "\\E", "\\exists", "\\e" ] Exists)
        , succeed Neg
            |. oneOfSymbols [ "-", "¬", "~" ]
            |. spaces
            |= lazy (\_ -> formula)
        , backtrackable <| lazy (\_ -> binary [ "&", "∧", "/\\" ] Conj)
        , backtrackable <| lazy (\_ -> binary [ "|", "∨", "\\/" ] Disj)
        , backtrackable <| lazy (\_ -> binary [ "->", "→" ] Impl)
        , succeed identity
            |. symbol "("
            |. spaces
            |= lazy (\_ -> formula)
            |. spaces
            |. symbol ")"
        ]


binary : List String -> (Formula -> Formula -> value) -> Parser value
binary conn constructor =
    succeed constructor
        |. symbol "("
        |. spaces
        |= lazy (\_ -> formula)
        |. spaces
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
    sequence
        { start = "("
        , separator = ","
        , end = ")"
        , spaces = spaces
        , item = term
        , trailing = Forbidden
        }


term : Parser Term
term =
    identifier
        |> Parser.andThen
            (\name ->
                oneOf
                    [ succeed (\fargs -> Fun name fargs)
                        |= lazy (\_ -> args)
                    , succeed (Var name)
                    ]
            )


identifier : Parser String
identifier =
    variable
        { start = isLetter
        , inner = isIdentChar
        , reserved = Set.empty
        }


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
    chompWhile (\c -> c == ' ' || c == '\t' || c == '\u{000D}' || c == '\u{000D}')


