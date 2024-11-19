module Main (main) where

import MyLib

import Data.Set (Set)
import qualified Data.Set as Set

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

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
test_paper = TestCase (assertEqual "Paper example" paper_output (dec paper_input))

tests :: Test
tests = TestList [TestLabel "Test paper" test_paper]

main :: IO ()
main = do
    result <- runTestTT tests
    if failures result > 0 then Exit.exitFailure else Exit.exitSuccess
