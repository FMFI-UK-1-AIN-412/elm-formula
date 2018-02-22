module TestFormula exposing (..)

import Test exposing (..)
import Expect
import Fuzz exposing (list, int, tuple, string)
import String
import Formula exposing (..)


fail msg =
    test msg <| \() -> Expect.true msg False


all : Test
all =
    describe "tableauEditor tests"
        [ strTermTests
        , strFormulaTests
        , strSignedTests
        , isSubformulaOfTests
        , parseTests
        , parseSignedTests
        ]


a : Formula
a =
    Atom "a" []


b : Formula
b =
    Atom "b" []


p : List Term -> Formula
p =
    Atom "ppp"


q : List Term -> Formula
q =
    Atom "q"


x : Term
x =
    Var "x"


y : Term
y =
    Var "yyy"


f : List Term -> Term
f =
    Fun "fff"


g : List Term -> Term
g =
    Fun "g"


strTTest : String -> Term -> Test
strTTest str f =
    test str <| \() -> Expect.equal str (strTerm f)


strTermTests : Test
strTermTests =
    describe "strTerm tests"
        [ strTTest "x" <| x
        , strTTest "fff(x,yyy)" <| f [ x, y ]
        , strTTest "fff()" <| f []
        , strTTest "fff(g(x,fff()),fff())" <| f [ g [ x, f [] ], f [] ]
        ]


strFTest : String -> Formula -> Test
strFTest str f =
    test str <| \() -> Expect.equal str (strFormula f)


strFormulaTests =
    describe "strFormula tests"
        [ strFTest "a" <| a
        , strFTest "¬a" <| Neg a
        , strFTest "(a∧b)" <| Conj a b
        , strFTest "(a∨b)" <| Disj a b
        , strFTest "(a→b)" <| Impl a b
        , strFTest "(¬(a→b)∨¬(b→a))" <| Disj (Neg (Impl a b)) (Neg (Impl b a))
        , strFTest "((a∧¬b)→(a∨(b→a)))" <| Impl (Conj a (Neg b)) (Disj a (Impl b a))
        , strFTest "∀x ppp(x)" <| ForAll "x" (p [ x ])
        , strFTest "∃x ppp(x)" <| Exists "x" (p [ x ])
        , strFTest "∀yyy ppp(x)" <| ForAll "yyy" (p [ x ])
        , strFTest "∃yyy ppp(x)" <| Exists "yyy" (p [ x ])
        ]


strSignedTest : String -> Signed Formula -> Test
strSignedTest str sf =
    test str <| \() -> Expect.equal str (strSigned sf)


strSignedTests =
    describe "strSigned tests"
        [ strSignedTest "F a" <| F a
        , strSignedTest "T a" <| T a
        ]


expecto =
    { patronum = Expect.true }


testSubformula failMsg1 failMsg2 assertion sub formula =
    let
        strSub =
            strFormula sub

        strF =
            strFormula formula
    in
        test ((strFormula sub) ++ " isSubformulaOf " ++ (strFormula formula)) <|
            \() ->
                assertion
                    (strSub ++ " is " ++ failMsg1 ++ "subformula of " ++ strF ++ " (when it should " ++ failMsg2 ++ "be)")
                    (isSubformulaOf sub formula)


testIsSubformula =
    testSubformula "not " "" expecto.patronum


testIsNotSubformula =
    testSubformula "" "not " Expect.false



{- Fuzzer? -}
{- a must not be subformula of b ;) -}


binIsSubformulaTests conn a b =
    [ testIsSubformula a (Conj a a)
    , testIsSubformula a (Conj a b)
    , testIsSubformula a (Conj b a)
    , testIsNotSubformula a (Conj b b)
    ]


isSubformulaOfTests =
    describe "isSubformulaOf tests"
        [ testIsNotSubformula a a
        , testIsSubformula a (Neg a)
        , testIsNotSubformula a (Neg b)
        , describe "Conj" <| binIsSubformulaTests Conj a b
        , describe "Disj" <| binIsSubformulaTests Conj a b
        , describe "Impl" <| binIsSubformulaTests Conj a b
        , describe "Conj bigger " <| binIsSubformulaTests Conj (Impl (Neg a) b) (Conj b (Neg a))
        , describe "Disj bigger " <| binIsSubformulaTests Disj (Impl (Neg a) b) (Disj b (Neg a))
        , describe "Impl bigger " <| binIsSubformulaTests Impl (Impl (Neg a) b) (Impl b (Neg a))
        , testIsSubformula (Impl a b) (ForAll "x" (Impl a b))
        , testIsSubformula (Impl a b) (Exists "x" (Impl a b))
        , testIsNotSubformula (Atom "x" []) (ForAll "x" (Impl a b))
        , testIsNotSubformula (Atom "x" []) (Exists "x" (Impl a b))
        ]


signedSubformulasTests =
    describe "signedSubformulas tests"
        [ test "T Neg" <| \() -> Expect.equal (signedSubformulas <| T <| Neg a) [ F a ]
        , test "F Neg" <| \() -> Expect.equal (signedSubformulas <| F <| Neg a) [ T a ]
        , test "T Conj" <| \() -> Expect.equal (signedSubformulas <| T <| Conj a b) [ T a, T b ]
        , test "F Conj" <| \() -> Expect.equal (signedSubformulas <| F <| Conj a b) [ F a, F b ]
        , test "T Disj" <| \() -> Expect.equal (signedSubformulas <| T <| Disj a b) [ T a, T b ]
        , test "F Disj" <| \() -> Expect.equal (signedSubformulas <| F <| Disj a b) [ F a, F b ]
        , test "T Impl" <| \() -> Expect.equal (signedSubformulas <| T <| Impl a b) [ F a, T b ]
        , test "F Impl" <| \() -> Expect.equal (signedSubformulas <| F <| Impl a b) [ T a, F b ]
        ]


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


parseTests =
    describe "parse tests"
        [ test "Neg " <| \() -> testParse "- a" <| Neg a
        , test "Disj" <| \() -> testParse "(a|b)" <| Disj a b
        , test "Conj" <| \() -> testParse "(a&b)" <| Conj a b
        , test "Impl" <| \() -> testParse "(a->b)" <| Impl a b
        , test "Complex formula" <|
            \() -> testParse "(-(a->b)|(b&a))" <| Disj (Neg (Impl a b)) (Conj b a)
        ]


parseSignedTests =
    describe "parseSigned tests"
        [ test "T a" <| \() -> testParseSigned "T a" <| T a
        , test "F a" <| \() -> testParseSigned "F a" <| F a
        ]



{- vim: set sw=2 ts=2 sts=2 et : -}
