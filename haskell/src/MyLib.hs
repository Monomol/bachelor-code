module MyLib where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Tuple (swap)
import Data.Maybe (fromJust)

import Data.SortedList (SortedList)
import qualified Data.SortedList as SortedList

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

-- coq functions fresh, elems
-- coq functions minuska var neco

data Term = Var String
    | Function String [Term]
    deriving (Show, Ord, Eq)


type Multiequation = (Set Term, MultiSet Term)
type Multiequations = Set Multiequation

type T =  [Multiequation]
type U = SortedList (Int, Multiequation)
type R = (T, U)

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

-- Algorithm UNIFY section

-- INITIALIZATION OF R

-- Predicates
isMEpmty :: Multiequation -> Bool
isMEpmty (_, x) = MultiSet.null x

-- Projections
termName :: Term -> String
termName (Var x) = x
termName (Function x _) = x

varsOfTerm :: Term ->  [Term]
varsOfTerm (Var x) = [Var x]
varsOfTerm (Function _ xs) = (concat . map varsOfTerm) xs

varsOfTerms :: [Term] -> [Term]
varsOfTerms xs = (concat . map varsOfTerm) xs

countedVarsOfTerms :: [Term] -> [(Int, Term)]
countedVarsOfTerms ts = ((map swap) . MultiSet.toAscOccurList . MultiSet.fromList . varsOfTerms) ts

uniqueTermName :: Term -> String
uniqueTermName (Var x) = x
uniqueTermName (Function x xs) = x ++ (concat . map uniqueTermName) xs

uniqueTermNameOverList :: [Term] -> String
uniqueTermNameOverList xs = (concat . map uniqueTermName) xs

-- Initiators
initMeq :: [Term] -> [Term] -> Int -> (Int, Multiequation)
initMeq vs ts occ = (occ, (Set.fromList vs, MultiSet.fromList ts))

initVarMeq :: (Int, Term) -> (Int, Multiequation)
initVarMeq (occ, t) = initMeq [t] [] occ

initU :: [Term] -> SortedList (Int, Multiequation)
initU ts = let firstMeq = initMeq [Var (uniqueTermNameOverList ts)] ts 0
               listOfVars = countedVarsOfTerms ts
               meqOfVars = map initVarMeq listOfVars in
    SortedList.toSortedList (firstMeq : meqOfVars)

initR :: [Term] -> ([Multiequation], SortedList (Int, Multiequation))
initR xs = ([], initU xs)

-- Picking S=M equation out of U
-- pick_lowest :: SortedList (Int, Multiequation) ->


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
