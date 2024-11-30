module Main (main) where

import MyLib

import Data.Set (Set)
import qualified Data.Set as Set

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

import Data.SortedList (SortedList)
import qualified Data.SortedList as SortedList

import Test.HUnit
import qualified System.Exit as Exit

paper_input :: MultiSet Term
paper_input = MultiSet.fromList [
    Function "f"
        [
            Var "x1",
            Function "g"
                [Function "a" [],
                    Function "f"
                        [ Var "x5", Function "b" [] ]
                ]
        ],
    Function "f"
        [
            Function "h"
                [ Function "c" [] ],
            Function "g"
                [Var "x2",
                    Function "f"
                        [ Function "b" [], Var "x5" ]
                ]
        ],
    Function "f"
        [
            Function "h"
                [ Var "x4" ],
            Function "g"
                [Var "x6",
                 Var "x3"
                ]
        ]
    ]

paper_output :: (Term, Multiequations)
paper_output = (Function "f" [Var "x1", Function "g" [Var "x2",Var "x3"]],
    Set.fromList [
        (Set.fromList [Var "x1"], MultiSet.fromOccurList [
            (Function "h" [Var "x4"],1),
            (Function "h" [Function "c" []],1)
            ]
        ),
        (Set.fromList [Var "x2", Var "x6"], MultiSet.fromOccurList [(Function "a" [],1)]),
        (Set.fromList [Var "x3"], MultiSet.fromOccurList [
            (Function "f" [Var "x5", Function "b" []],1),
            (Function "f" [Function "b" [], Var "x5"],1)
            ])
        ]
    )

test_paper :: Test
test_paper = TestCase (assertEqual "" paper_output (dec paper_input))

unit1_input :: MultiSet Term
unit1_input = MultiSet.fromList [
    Var "x1",
    Function "f" [Function "a" []]
    ]

unit1_output :: (Term, Multiequations)
unit1_output = (Var "x1", Set.fromList [ (Set.fromList [Var "x1"], MultiSet.fromList [Function "f" [Function "a" []]]) ] )

test_unit1 :: Test
test_unit1 = TestCase (assertEqual "" unit1_output (dec unit1_input))

unit2_input :: MultiSet Term
unit2_input = MultiSet.fromList [
    Function "f" [Function "a" []],
    Function "f" [Function "a" []]
    ]

unit2_output :: (Term, Multiequations)
unit2_output = (Function "f" [Function "a" []], Set.empty)

test_unit2 :: Test
test_unit2 = TestCase (assertEqual "" unit2_output (dec unit2_input))

terms_to_unify_paper_input :: [Term]
terms_to_unify_paper_input = [
    Function "f" [Var "x1", Function "g" [Var "x2", Var "x3"], Var "x2", Function "b" []],
    Function "f" [Function "g" [Function "h" [Function "a" [], Var "x5"], Var "x2"], Var "x1", Function "h" [Function "a" [], Var "x4"], Var "x4"]
    ]

terms_to_unify_paper_output :: SortedList (Int, Multiequation)
terms_to_unify_paper_output = SortedList.toSortedList [
    (0, (Set.singleton (Var "fx1gx2x3x2bfghax5x2x1hax4x4"), MultiSet.fromList terms_to_unify_paper_input)),
    (2, (Set.singleton (Var "x1"), MultiSet.empty)),
    (3, (Set.singleton (Var "x2"), MultiSet.empty)),
    (1, (Set.singleton (Var "x3"), MultiSet.empty)),
    (2, (Set.singleton (Var "x4"), MultiSet.empty)),
    (1, (Set.singleton (Var "x5"), MultiSet.empty))
    ]

test_initR :: Test
test_initR = TestCase (assertEqual "" ([], terms_to_unify_paper_output) (initR terms_to_unify_paper_input))

terms_remove_paper_beginning_output :: ((Int, Multiequation), SortedList (Int, Multiequation))
terms_remove_paper_beginning_output = ((0, (Set.singleton (Var "fx1gx2x3x2bfghax5x2x1hax4x4"), MultiSet.fromList terms_to_unify_paper_input)), SortedList.toSortedList [
    (0, (Set.singleton (Var "x1"), MultiSet.empty)),
    (0, (Set.singleton (Var "x2"), MultiSet.empty)),
    (0, (Set.singleton (Var "x3"), MultiSet.empty)),
    (0, (Set.singleton (Var "x4"), MultiSet.empty)),
    (0, (Set.singleton (Var "x5"), MultiSet.empty))
    ])

test_remove_paper_beginning :: Test
test_remove_paper_beginning = TestCase (assertEqual "" terms_remove_paper_beginning_output (removeMulEquation terms_to_unify_paper_output))

terms_remove_unit1_input :: SortedList (Int, Multiequation)
terms_remove_unit1_input = SortedList.toSortedList [
    (0, (Set.singleton (Var "x"), MultiSet.singleton (Function "f" [Var "x1", Var "x1", Var "x1"]))),
    (3, (Set.singleton (Var "x1"), MultiSet.empty))
    ]

terms_remove_unit1_output :: ((Int, Multiequation), SortedList (Int, Multiequation))
terms_remove_unit1_output = ((0, (Set.singleton (Var "x"), MultiSet.singleton (Function "f" [Var "x1", Var "x1", Var "x1"]))),
    SortedList.toSortedList [
        (0, (Set.singleton (Var "x1"), MultiSet.empty))
    ])

test_terms_remove_unit1 :: Test
test_terms_remove_unit1 = TestCase (assertEqual "" terms_remove_unit1_output (removeMulEquation terms_remove_unit1_input))


tests :: Test
tests = TestList [
    TestLabel "DEC Test paper" test_paper,
    TestLabel "DEC Unit 1" test_unit1,
    TestLabel "DEC Unit 2" test_unit2,
    -- 
    TestLabel "INIT R Test paper" test_initR,
    --
    TestLabel "REMOVE MEQ FROM U Test paper" test_remove_paper_beginning,
    TestLabel "REMOVE MEQ FROM U Unit 1" test_terms_remove_unit1
    ]

main :: IO ()
main = do
    result <- runTestTT tests
    if failures result > 0 then Exit.exitFailure else Exit.exitSuccess
