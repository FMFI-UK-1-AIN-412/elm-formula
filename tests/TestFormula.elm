module TestFormula exposing (..)

import Dict
import Expect
import Formula exposing (..)
import Formula.Parser
import Formula.Signed exposing (Signed(..))
import Fuzz exposing (int, list, string, tuple)
import Parser
import String
import Term exposing (Substitution, Term(..))
import Test exposing (..)


fail msg =
    test msg <| \() -> Expect.true msg False


a : Formula
a =
    Atom "a" []


b : Formula
b =
    Atom "b" []


d : Term
d =
    Var "d"


j : Term
j =
    Var "j"


pt : Term
pt =
    Var "pt"


p : List Term -> Formula
p =
    Atom "ppp"


s : Term
s =
    Var "s"


q : List Term -> Formula
q =
    Atom "q"


k : Term
k =
    Var "k"


x : Term
x =
    Var "x"


y : Term
y =
    Var "yyy"


z : Term
z =
    Var "z"


f : List Term -> Term
f =
    Fun "fff"


g : List Term -> Term
g =
    Fun "g"


strTTest : String -> Term -> Test
strTTest str term =
    test str <| \() -> Expect.equal str (Term.toString term)


strTermTests : Test
strTermTests =
    describe "strTerm tests"
        [ strTTest "x" <| x
        , strTTest "fff(x,yyy)" <| f [ x, y ]
        , strTTest "fff()" <| f []
        , strTTest "fff(g(x,fff()),fff())" <| f [ g [ x, f [] ], f [] ]
        ]


strFTest : String -> Formula -> Test
strFTest str formula =
    test str <| \() -> Expect.equal str (Formula.toString formula)


strFormulaTests : Test
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
    test str <| \() -> Expect.equal str (Formula.Signed.toString sf)


strSignedTests : Test
strSignedTests =
    describe "strSigned tests"
        [ strSignedTest "F a" <| F a
        , strSignedTest "T a" <| T a
        ]


testSubformula failMsg1 failMsg2 assertion sub formula =
    let
        strSub =
            Formula.toString sub

        strF =
            Formula.toString formula
    in
    test (Formula.toString sub ++ " isSubformulaOf " ++ Formula.toString formula) <|
        \() ->
            assertion
                (strSub ++ " is " ++ failMsg1 ++ "subformula of " ++ strF ++ " (when it should " ++ failMsg2 ++ "be)")
                (isSubformulaOf sub formula)


testIsSubformula =
    testSubformula "not " "" Expect.true


testIsNotSubformula =
    testSubformula "" "not " Expect.false



{- Fuzzer? -}
{- a must not be subformula of b ;) -}


binIsSubformulaTests conn fa fb =
    [ testIsSubformula fa (Conj fa fa)
    , testIsSubformula fa (Conj fa fb)
    , testIsSubformula fa (Conj fb fa)
    , testIsNotSubformula fa (Conj fb fb)
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
        [ test "T Neg" <| \() -> Expect.equal (Formula.Signed.subformulas <| T <| Neg a) [ F a ]
        , test "F Neg" <| \() -> Expect.equal (Formula.Signed.subformulas <| F <| Neg a) [ T a ]
        , test "T Conj" <| \() -> Expect.equal (Formula.Signed.subformulas <| T <| Conj a b) [ T a, T b ]
        , test "F Conj" <| \() -> Expect.equal (Formula.Signed.subformulas <| F <| Conj a b) [ F a, F b ]
        , test "T Disj" <| \() -> Expect.equal (Formula.Signed.subformulas <| T <| Disj a b) [ T a, T b ]
        , test "F Disj" <| \() -> Expect.equal (Formula.Signed.subformulas <| F <| Disj a b) [ F a, F b ]
        , test "T Impl" <| \() -> Expect.equal (Formula.Signed.subformulas <| T <| Impl a b) [ F a, T b ]
        , test "F Impl" <| \() -> Expect.equal (Formula.Signed.subformulas <| F <| Impl a b) [ T a, F b ]
        ]


testParseFunction function string formula =
    case function string of
        Ok value ->
            Expect.equal value formula

        Err error ->
            Expect.fail <| "Parsing failed: " ++ Parser.deadEndsToString error


testParse =
    testParseFunction Formula.Parser.parse


testParseSigned =
    testParseFunction Formula.Parser.parseSigned


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



--testovanie spravneho dosadenia


testSubstitution : Substitution -> Formula -> Formula -> Test
testSubstitution subst original new =
    test
        ("in formula " ++ (original |> Formula.toString) ++ " using subs " ++ Term.strSubstitution subst)
        (\() -> Expect.equal (Ok new) (Formula.substitute subst original))



--testovanie spravneho vyberu premennych -> aplikovateľnosť substitúcie


testSubstitutionFail : Substitution -> Formula -> Test
testSubstitutionFail subst original =
    test
        ("substitution is not applicable in "
            ++ Formula.toString original
            ++ " by substituting "
            ++ Term.strSubstitution subst
        )
        (\() -> Expect.err (Formula.substitute subst original))


testRemoveQuantifierAndSubstitute : Substitution -> Formula -> Formula -> Test
testRemoveQuantifierAndSubstitute subst original new =
    test
        ("in formula " ++ (original |> Formula.toString) ++ " using subs " ++ Term.strSubstitution subst)
        (\() -> Expect.equal (Ok new) (Formula.removeQuantifierAndSubstitute subst original))


testRemoveQuantifierAndSubstituteFail : Substitution -> Formula -> Test
testRemoveQuantifierAndSubstituteFail subst original =
    test
        ("in formula " ++ (original |> Formula.toString) ++ " using subs " ++ Term.strSubstitution subst)
        (\() -> Expect.err (Formula.removeQuantifierAndSubstitute subst original))



--testovanie substitucie viacerych premennych naraz


substitutionTests =
    describe "Substitution "
        [ --normal
          testSubstitution
            (Dict.fromList [ ( "d", y ), ( "j", x ) ])
            (Impl
                (Disj
                    (ForAll "d" (Atom "P" [ d, Fun "f" [ d ], pt ]))
                    (ForAll "j" (Atom "J" [ j, pt ]))
                )
                (Atom "S" [ s, j, Fun "d" [ d ] ])
            )
            (Impl
                (Disj
                    (ForAll "d" (Atom "P" [ d, Fun "f" [ d ], pt ]))
                    (ForAll "j" (Atom "J" [ j, pt ]))
                )
                (Atom "S" [ s, x, Fun "d" [ y ] ])
            )
        , testSubstitution
            (Dict.fromList [ ( "pt", x ) ])
            (Neg (Conj (Neg (Atom "P" [ pt ])) (Atom "Z" [ x ])))
            (Neg (Conj (Neg (Atom "P" [ x ])) (Atom "Z" [ x ])))
        , testSubstitution
            (Dict.fromList [ ( "x", Var "k" ) ])
            (Formula.Parser.parse "\\forall x \\forall k P(x,k)" |> Result.withDefault FF)
            (Formula.Parser.parse "\\forall x \\forall k P(x,k)" |> Result.withDefault FF)
        , testSubstitution
            (Dict.fromList [ ( "x", d ), ( "d", x ) ])
            (Formula.Parser.parse "\\forall x \\forall d P(x,d)" |> Result.withDefault FF)
            (Formula.Parser.parse "\\forall x \\forall d P(x,d)" |> Result.withDefault FF)

        -- naraz
        , testSubstitution
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (Disj (Atom "P" [ x ]) (Atom "R" [ y ]))
            --P(x) | R(y)
            (Disj (Atom "P" [ y ]) (Atom "R" [ x ]))
        , testSubstitution
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (Atom "P" [ x, y ])
            -- P(x,y)
            (Atom "P" [ y, x ])
        , testSubstitution
            (Dict.fromList [ ( "x", y ), ( "yyy", s ), ( "s", x ) ])
            (Disj (Atom "P" [ x, y ]) (Atom "L" [ y, s ]))
            (Disj (Atom "P" [ y, s ]) (Atom "L" [ s, x ]))
        , testSubstitution
            (Dict.fromList [ ( "x", k ), ( "yyy", z ) ])
            (ForAll "x" (Exists "yyy" (Atom "P" [ x, y ])))
            (ForAll "x" (Exists "yyy" (Atom "P" [ x, y ])))

        --viazane premenne
        , testSubstitution
            (Dict.fromList [ ( "x", s ) ])
            (Conj (Atom "P" [ x ]) (ForAll "x" (Atom "Q" [ x ])))
            (Conj (Atom "P" [ s ]) (ForAll "x" (Atom "Q" [ x ])))
        , testSubstitution
            (Dict.fromList [ ( "x", s ) ])
            (Impl (ForAll "x" (Atom "P" [ x ])) (Atom "P" [ x, pt ]))
            (Impl (ForAll "x" (Atom "P" [ x ])) (Atom "P" [ s, pt ]))

        --subst nie je aplikovatelna
        , testSubstitutionFail
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "k" (Atom "P" [ x, k ]))
        , testSubstitutionFail
            (Dict.fromList [ ( "z", pt ) ])
            (ForAll "pt" (Disj (Atom "P" [ z, k, x ]) (Atom "R" [ z, pt ])))
        , testSubstitutionFail
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "pt" (Conj (ForAll "z" (Atom "P" [ pt, z, x ])) (Exists "k" (Atom "R" [ pt, z, k ]))))
        ]


removeQuantifierTests =
    describe "Remove quantifier and substitute"
        [ testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (ForAll "x" (ForAll "yyy" (Atom "P" [ x, y ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (ForAll "x" (Exists "yyy" (Atom "P" [ x, y ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "z" (Disj (Atom "P" [ z ]) (ForAll "x" (Atom "P" [ x ]))))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (Atom "P" [ z ]) (ForAll "k" (Atom "P" [ k, z ]))))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", Var "k" ) ])
            (ForAll "x" (Exists "k" (Atom "P" [ Var "k", Var "x" ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "d", z ) ])
            (ForAll "x" (Exists "d" (Atom "P" [ x, d ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Atom "P" [ x ]))
            (Atom "P" [ k ])
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Disj (Atom "P" [ x ]) (Atom "R" [ x ])))
            (Disj (Atom "P" [ k ]) (Atom "R" [ k ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Disj (Atom "P" [ x ]) (Atom "P" [ z ])))
            (Disj (Atom "P" [ k ]) (Atom "P" [ z ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Disj (Atom "P" [ x ]) (ForAll "z" (Atom "P" [ z ]))))
            (Disj (Atom "P" [ k ]) (ForAll "z" (Atom "P" [ z ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (Atom "P" [ z ]) (ForAll "z" (Atom "G" [ z ]))))
            (Disj (Atom "P" [ k ]) (ForAll "z" (Atom "G" [ z ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (Atom "P" [ z ]) (ForAll "x" (Atom "P" [ x ]))))
            (Disj (Atom "P" [ k ]) (ForAll "x" (Atom "P" [ x ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (Atom "P" [ z ]) (Atom "P" [ k ])))
            (Disj (Atom "P" [ k ]) (Atom "P" [ k ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Atom "P" [ Fun "f" [ x ] ]))
            (Atom "P" [ Fun "f" [ k ] ])
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Exists "yyy" (Atom "P" [ x, y ])))
            (Exists "yyy" (Atom "P" [ k, y ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", Var "k" ) ])
            (ForAll "x" (Atom "P" [ Var "x", Var "k" ]))
            (Atom "P" [ Var "k", Var "k" ])
        ]



{- vim: set sw=2 ts=2 sts=2 et : -}
