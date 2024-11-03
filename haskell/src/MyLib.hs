module MyLib (dec) where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

data Formula = Var String
    | Term String
    | Function String [Formula]
    deriving (Show, Ord, Eq)


type Multiequation = (Set Formula, MultiSet Formula)
type Multiequations = Set Multiequation

cp_frontier_example :: MultiSet Formula
cp_frontier_example = MultiSet.fromList [
    Function "f"
        [
            Var "x1",
            Function "g"
                [Term "a",
                    Function "f"
                        [ Var "x5", Term "b" ]
                ]
        ],
    Function "f"
        [
            Function "h"
                [ Term "c" ],
            Function "g"
                [Var "x2",
                    Function "f"
                        [ Term "b", Var "x5" ]
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

-- Predicates
isTerm :: Formula -> Bool
isTerm (Term _) = True
isTerm _ = False

isVar :: Formula -> Bool
isVar (Var _) = True
isVar _ = False

-- Projections
fHead :: Formula -> String
fHead (Term x) = x
fHead (Function x _) = x
fHead _ = error "not a function" -- corresponds to the definition from paper

fArgs :: Formula -> [Formula]
fArgs (Function _ x) = x

-- Properties
fArity :: Formula -> Int
fArity (Function _ x) = length x

-- Convertors
splitVarNonVar :: MultiSet Formula -> (MultiSet Formula, MultiSet Formula)
splitVarNonVar x = MultiSet.partition isVar x

-- set should be used here on the left-hand side
dec :: MultiSet Formula -> (Formula, Multiequations)
dec m = let varMultiset = fst . splitVarNonVar
            nonVarMultiset = snd . splitVarNonVar in (
            if (not . MultiSet.null . varMultiset) m then 
                ((head . MultiSet.elems . varMultiset) m, (Set.singleton . makeMultEq) m)
            else
                -- below efficiency can be improved
                let funcs = (MultiSet.distinctElems . nonVarMultiset) m
                    funcNames = (nub . (map fHead)) funcs
                    disFuncsAmount = length funcNames
                    fstFunc = head funcs in (
                    if disFuncsAmount == 1 then
                        if isTerm fstFunc then
                            (fstFunc, Set.empty :: Multiequations)
                        else
                            let funcArgs = MultiSet.fold (\x y -> (fArgs x):y) [] m
                                mn = (transpose . reverse) funcArgs
                                mnSet = (map (\x -> MultiSet.fromList x)) mn in (
                                    ((Function (fHead fstFunc) (map (fst . dec) mnSet)), (Set.unions . (map (snd . dec))) mnSet)
                            )
                    else
                        error "multiple function symbols exist"
                    )
                )
                where
                    mulSetTupToMultEq (l, r) = (MultiSet.toSet l, r)
                    makeMultEq x = (mulSetTupToMultEq . splitVarNonVar) x


res = dec cp_frontier_example

encapsulate :: String -> String -> [String] -> String
encapsulate l r xs = l ++ (intercalate ", ") xs ++ r

extract_term :: Formula -> String
extract_term (Term x) = x
extract_term (Var x) = x 
extract_term (Function x xs) = x ++ encapsulate "(" ")" (map extract_term xs)

print_sm :: (Formula, Multiequations) -> IO()
print_sm (f, set_sm) = putStrLn ("Common part\n    " ++ extract_term f ++ "\nFrontier\n{\n" ++ print_set_sm (Set.elems set_sm) ++ "}")
    where
        print_m m = ((encapsulate "{ " " }") . (map extract_term) . Set.elems) m
        print_s s = ((encapsulate "( " " )") . (map extract_term) . MultiSet.distinctElems) s
        print_set_sm [] = ""
        print_set_sm ((m, s):sm) = "    " ++ print_m m ++ " = " ++ print_s s ++ ",\n" ++ print_set_sm sm
