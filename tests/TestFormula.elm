module TestFormula exposing (..)

import Dict
import Expect
import Formula exposing (Formula(..))
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
    PredAtom "a" []


b : Formula
b =
    PredAtom "b" []


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
    PredAtom "ppp"


s : Term
s =
    Var "s"


q : List Term -> Formula
q =
    PredAtom "q"


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
        , strFTest "d≐j" <| EqAtom d j
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
                (Formula.isSubformulaOf sub formula)


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
        , testIsNotSubformula (EqAtom d j) (EqAtom d j)
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
        , testIsNotSubformula (PredAtom "x" []) (ForAll "x" (Impl a b))
        , testIsNotSubformula (PredAtom "x" []) (Exists "x" (Impl a b))
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
        [ test "Eq" <| \() -> testParse "(d≐j)" <| EqAtom d j 
        , test "Neg " <| \() -> testParse "- a" <| Neg a
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
                    (ForAll "d" (PredAtom "P" [ d, Fun "f" [ d ], pt ]))
                    (ForAll "j" (PredAtom "J" [ j, pt ]))
                )
                (PredAtom "S" [ s, j, Fun "d" [ d ] ])
            )
            (Impl
                (Disj
                    (ForAll "d" (PredAtom "P" [ d, Fun "f" [ d ], pt ]))
                    (ForAll "j" (PredAtom "J" [ j, pt ]))
                )
                (PredAtom "S" [ s, x, Fun "d" [ y ] ])
            )
        , testSubstitution
            (Dict.fromList [ ( "pt", x ) ])
            (Neg (Conj (Neg (PredAtom "P" [ pt ])) (PredAtom "Z" [ x ])))
            (Neg (Conj (Neg (PredAtom "P" [ x ])) (PredAtom "Z" [ x ])))
        , testSubstitution
            (Dict.fromList [ ( "pt", x ) ])
            (Neg (Conj (Neg (EqAtom pt d)) (EqAtom pt j)))
            (Neg (Conj (Neg (EqAtom x d)) (EqAtom x j)))
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
            (Disj (PredAtom "P" [ x ]) (PredAtom "R" [ y ]))
            --P(x) | R(y)
            (Disj (PredAtom "P" [ y ]) (PredAtom "R" [ x ]))
        , testSubstitution
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (PredAtom "P" [ x, y ])
            -- P(x,y)
            (PredAtom "P" [ y, x ])
        , testSubstitution
            (Dict.fromList [ ( "x", y ), ( "yyy", s ), ( "s", x ) ])
            (Disj (PredAtom "P" [ x, y ]) (PredAtom "L" [ y, s ]))
            (Disj (PredAtom "P" [ y, s ]) (PredAtom "L" [ s, x ]))
        , testSubstitution
            (Dict.fromList [ ( "x", k ), ( "yyy", z ) ])
            (ForAll "x" (Exists "yyy" (PredAtom "P" [ x, y ])))
            (ForAll "x" (Exists "yyy" (PredAtom "P" [ x, y ])))
        , testSubstitution
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (Disj (EqAtom x d) (EqAtom y j))
            (Disj (EqAtom y d) (EqAtom x j))

        --viazane premenne
        , testSubstitution
            (Dict.fromList [ ( "x", s ) ])
            (Conj (PredAtom "P" [ x ]) (ForAll "x" (PredAtom "Q" [ x ])))
            (Conj (PredAtom "P" [ s ]) (ForAll "x" (PredAtom "Q" [ x ])))
        , testSubstitution
            (Dict.fromList [ ( "x", s ) ])
            (Impl (ForAll "x" (PredAtom "P" [ x ])) (PredAtom "P" [ x, pt ]))
            (Impl (ForAll "x" (PredAtom "P" [ x ])) (PredAtom "P" [ s, pt ]))
        , testSubstitution
            (Dict.fromList [ ( "x", s ) ])
            (Conj (EqAtom d x) (ForAll "x" (EqAtom x j)))
            (Conj (EqAtom d s) (ForAll "x" (EqAtom x j)))

        --subst nie je aplikovatelna
        , testSubstitutionFail
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "k" (PredAtom "P" [ x, k ]))
        , testSubstitutionFail
            (Dict.fromList [ ( "z", pt ) ])
            (ForAll "pt" (Disj (PredAtom "P" [ z, k, x ]) (PredAtom "R" [ z, pt ])))
        , testSubstitutionFail
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "pt" (Conj (ForAll "z" (PredAtom "P" [ pt, z, x ])) (Exists "k" (PredAtom "R" [ pt, z, k ]))))
        , testSubstitutionFail
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "k" (EqAtom x k))
        ]


removeQuantifierTests =
    describe "Remove quantifier and substitute"
        [ testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (ForAll "x" (ForAll "yyy" (PredAtom "P" [ x, y ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (ForAll "x" (Exists "yyy" (PredAtom "P" [ x, y ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "z" (Disj (PredAtom "P" [ z ]) (ForAll "x" (PredAtom "P" [ x ]))))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (PredAtom "P" [ z ]) (ForAll "k" (PredAtom "P" [ k, z ]))))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", Var "k" ) ])
            (ForAll "x" (Exists "k" (PredAtom "P" [ Var "k", Var "x" ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "d", z ) ])
            (ForAll "x" (Exists "d" (PredAtom "P" [ x, d ])))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", y ), ( "yyy", x ) ])
            (ForAll "x" (ForAll "yyy" (EqAtom x y)))
        , testRemoveQuantifierAndSubstituteFail
            (Dict.fromList [ ( "x", Var "k" ) ])
            (ForAll "x" (Exists "k" (EqAtom k x)))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (PredAtom "P" [ x ]))
            (PredAtom "P" [ k ])
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Disj (PredAtom "P" [ x ]) (PredAtom "R" [ x ])))
            (Disj (PredAtom "P" [ k ]) (PredAtom "R" [ k ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Disj (PredAtom "P" [ x ]) (PredAtom "P" [ z ])))
            (Disj (PredAtom "P" [ k ]) (PredAtom "P" [ z ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Disj (PredAtom "P" [ x ]) (ForAll "z" (PredAtom "P" [ z ]))))
            (Disj (PredAtom "P" [ k ]) (ForAll "z" (PredAtom "P" [ z ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (PredAtom "P" [ z ]) (ForAll "z" (PredAtom "G" [ z ]))))
            (Disj (PredAtom "P" [ k ]) (ForAll "z" (PredAtom "G" [ z ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (PredAtom "P" [ z ]) (ForAll "x" (PredAtom "P" [ x ]))))
            (Disj (PredAtom "P" [ k ]) (ForAll "x" (PredAtom "P" [ x ])))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "z", k ) ])
            (ForAll "z" (Disj (PredAtom "P" [ z ]) (PredAtom "P" [ k ])))
            (Disj (PredAtom "P" [ k ]) (PredAtom "P" [ k ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (PredAtom "P" [ Fun "f" [ x ] ]))
            (PredAtom "P" [ Fun "f" [ k ] ])
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Exists "yyy" (PredAtom "P" [ x, y ])))
            (Exists "yyy" (PredAtom "P" [ k, y ]))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", Var "k" ) ])
            (ForAll "x" (PredAtom "P" [ Var "x", Var "k" ]))
            (PredAtom "P" [ Var "k", Var "k" ])
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", k ) ])
            (ForAll "x" (Exists "yyy" (EqAtom x y)))
            (Exists "yyy" (EqAtom k y))
        , testRemoveQuantifierAndSubstitute
            (Dict.fromList [ ( "x", Var "k" ) ])
            (ForAll "x" (EqAtom x k))
            (EqAtom k k)
        ]



{- vim: set sw=2 ts=2 sts=2 et : -}
