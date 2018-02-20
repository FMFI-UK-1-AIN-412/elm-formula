module TestFormula exposing (..)

import Expect exposing (Expectation)
import Fuzz exposing (Fuzzer, int, list, string)
import Test exposing (..)
import Formula


testParseFunction function string formula =
    case function string of
        Ok value ->
            Expect.equal value formula

        Err error ->
            Expect.fail <| "Parsing failed: " ++ toString error


testParse =
    testParseFunction Formula.parse


testParseSigned =
    testParseFunction Formula.parseSigned


suite : Test
suite =
    describe "Test Formula module"
        [ describe "Parse formulas"
            [ test "Parse negation - new " <|
                \_ -> testParse "- a" (Formula.Neg (Formula.Atom "a"))
            , test "Parse or" <|
                \_ ->
                    testParse "(a|b)" (Formula.Disj (Formula.Atom "a") (Formula.Atom "b"))
            , test "Parse and" <|
                \_ -> testParse "(a&b)" (Formula.Conj (Formula.Atom "a") (Formula.Atom "b"))
            , test "Parse implication" <|
                \_ -> testParse "(a->b)" (Formula.Impl (Formula.Atom "a") (Formula.Atom "b"))
            , test "Parse complicated formula" <|
                \_ ->
                    testParse "(-(a->b)|(a&c))"
                        (Formula.Disj
                            (Formula.Neg (Formula.Impl (Formula.Atom "a") (Formula.Atom "b")))
                            (Formula.Conj (Formula.Atom "a") (Formula.Atom "c"))
                        )
            ]
        , describe "Parse signed formulas"
            [ test "Parse true formula" <|
                \_ -> testParseSigned "T a" (Formula.T <| Formula.Atom "a")
            , test "Parse false formula" <|
                \_ -> testParseSigned "F a" (Formula.F <| Formula.Atom "a")
            ]
        ]
