module MyLib (dec) where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

-- make term to function, rename formula to term
data Term = Var String
    | Function String [Term]
    deriving (Show, Ord, Eq)


type Multiequation = (Set Term, MultiSet Term)
type Multiequations = Set Multiequation

cp_frontier_example :: MultiSet Term
cp_frontier_example = MultiSet.fromList [
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

-- Predicates
isConstant :: Term -> Bool
isConstant (Function _ []) = True
isConstant _ = False

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

-- Projections
fHead :: Term -> String
fHead (Function x _) = x
fHead _ = error "not a function" -- corresponds to the definition from paper

fParams :: Term -> [Term]
fParams (Function _ x) = x

-- Properties
fArity :: Term -> Int
fArity (Function _ x) = length x

-- Convertors
splitVarNonVar :: MultiSet Term -> (MultiSet Term, MultiSet Term)
splitVarNonVar x = MultiSet.partition isVar x

finalFormConv :: (MultiSet Term, MultiSet Term) -> (Set Term, MultiSet Term)
finalFormConv (l, r) = (MultiSet.toSet l, r)

makeMultEq :: MultiSet Term -> (Set Term, MultiSet Term)
makeMultEq x = (finalFormConv . splitVarNonVar) x

-- set should be used here on the left-hand side
dec :: MultiSet Term -> (Term, Multiequations)
dec m = let varMultiset = fst . splitVarNonVar
            nonVarMultiset = snd . splitVarNonVar in (
            if (not . MultiSet.null . varMultiset) m then 
                ((head . MultiSet.elems . varMultiset) m, (Set.singleton . makeMultEq) m)
            else
                let funcs = (MultiSet.distinctElems . nonVarMultiset) m
                    funcNames = (nub . (map fHead)) funcs
                    disFuncsAmount = length funcNames
                    fstFunc = head funcs in (
                    if disFuncsAmount == 1 then
                        if isConstant fstFunc then
                            (fstFunc, Set.empty :: Multiequations)
                        else
                            let funcParams = MultiSet.fold (\x y -> (fParams x):y) [] m
                                mi = (transpose . reverse) funcParams -- reverse undoes reversion in the previous fold
                                miMulSet = map MultiSet.fromList mi
                                miCParams = map (fst . dec) miMulSet
                                miFrontEqs = map (snd . dec) miMulSet
                                in (
                                    ((Function (fHead fstFunc) miCParams), Set.unions miFrontEqs)
                            )
                    else
                        error "multiple function symbols exist"
                    )
                )

encapsulate :: String -> String -> [String] -> String
encapsulate l r xs = l ++ (intercalate ", ") xs ++ r

extract_term :: Term -> String
extract_term (Var x) = x
extract_term (Function x []) = x 
extract_term (Function x xs) = x ++ encapsulate "(" ")" (map extract_term xs)

print_sm :: (Term, Multiequations) -> IO()
print_sm (f, set_sm) = putStrLn ("Common part\n    " ++ extract_term f ++ "\nFrontier\n{\n" ++ print_set_sm (Set.elems set_sm) ++ "}")
    where
        print_m m = ((encapsulate "{ " " }") . (map extract_term) . Set.elems) m
        print_s s = ((encapsulate "( " " )") . (map extract_term) . MultiSet.distinctElems) s
        print_set_sm [] = ""
        print_set_sm ((m, s):sm) = "    " ++ print_m m ++ " = " ++ print_s s ++ ",\n" ++ print_set_sm sm

res = dec cp_frontier_example
