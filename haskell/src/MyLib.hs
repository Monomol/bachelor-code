module MyLib where

import Data.List

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Tuple (swap)
import Data.Maybe (fromJust, isNothing)

import Data.SortedList (SortedList)
import qualified Data.SortedList as SortedList

import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet

-- questions:
--  - formulate the base (relation to set of equations)
--   - term equality if identical (kulmon paper) - through some equality or proposition?
--   - two operations (variable elimination, term reduction) creating SE' equivalent to SE
--  - how to implement compactification
--  - ask about ltac1 solvers and rewrites, auto, use of ; instead of ., exact, revert, clear, subst, assumption
--  - ideal work flow (time of finishing pillars)

-- coq functions fresh, elems
-- coq functions minuska varsof

data Term = Var String
    | Function String [Term]
    deriving (Show, Ord, Eq)

-- Multiequation is valid iff S is non-empty set of variables and T is mutliset of non-variable terms
type Multiequation = (Set Term, MultiSet Term)
type Multiequations = Set Multiequation


-- T is valid iff T contains valid multiequations, right sides of T have at most one element and all elements in left sides of T
-- can only occur in the right hand sides of T in equations PRECEDING this multiequation
type T =  [Multiequation]
-- U is valid iff U contains valid multiequations
type U = SortedList (Int, Multiequation)
-- R system is valid iff T is valid and U is valid, left sides of T and U are disjoint, and contain all variables (this should be concludable from relation to set of equations SE)
type R = (T, U)

-- Predicates
isConstant :: Term -> Bool
isConstant (Function _ []) = True
isConstant _ = False

isVar :: Term -> Bool
isVar (Var _) = True
isVar _ = False

hasSingleElem :: [a] -> Bool
hasSingleElem [_] = True
hasSingleElem _ = False

-- Projections
fHead :: Term -> String
fHead (Function x _) = x
fHead _ = error "not a function" -- corresponds to the definition from paper

fParams :: Term -> [Term]
fParams (Function _ x) = x
fParams _ = error "not a function"

-- Properties
fArity :: Term -> Int
fArity (Function _ x) = length x
fArity _ = error "not a function"

-- Convertors
splitVarNonVar :: MultiSet Term -> (MultiSet Term, MultiSet Term)
splitVarNonVar x = MultiSet.partition isVar x

finalFormConv :: (MultiSet Term, MultiSet Term) -> (Set Term, MultiSet Term)
finalFormConv (l, r) = (MultiSet.toSet l, r)

makeMultEq :: MultiSet Term -> (Set Term, MultiSet Term)
makeMultEq x = (finalFormConv . splitVarNonVar) x


-- Assumptions:
--  * input is valid right side of multiequation
--  * input corresponds to some set of equations SE (implies that that all terms t_r,t_s from M are in relation of RST closure of Rse)
-- Conclusions:
--  * output corresponds to the same set of equations SE
--  * output set of multiequations is valid


-- How to prove it? By showing that each step is reversible, which means
-- TODO: this function very likely fails on empty input.
dec :: MultiSet Term -> (Term, Multiequations)
-- here it would be better to use tuple unpacking
dec m = let (varMultiset, nonVarMultiset) = splitVarNonVar m in (
            if (not . MultiSet.null) varMultiset then 
                ((head . MultiSet.elems) varMultiset, (Set.singleton . makeMultEq) m)
            else
                let funcs = (MultiSet.distinctElems) nonVarMultiset
                    funcNames = (nub . map fHead) funcs
                    headFuncs = head funcs in (
                    if hasSingleElem funcNames then
                        if isConstant headFuncs then
                            (headFuncs, Set.empty :: Multiequations)
                        else
                            let funcParams = MultiSet.fold (\x y -> (fParams x):y) [] m
                                mi = (transpose . reverse) funcParams -- reverse undoes reversion in the previous fold
                                miMulSet = map MultiSet.fromList mi
                                (miCParams, miFrontEqs) = (unzip . map dec) miMulSet
                                in (
                                    ((Function (fHead headFuncs) miCParams), Set.unions miFrontEqs)
                            )
                    else
                        error "multiple function symbols exist"
                    )
                )

-- Algorithm UNIFY section

-- INITIALIZATION OF R

-- Predicates
mulEqIntersect :: Multiequation -> Multiequation -> Bool
mulEqIntersect (s1, _) (s2, _) = (not . Set.disjoint s1) s2

uMulEqIntersect :: (Int, Multiequation) -> (Int, Multiequation) -> Bool
uMulEqIntersect (_, ms1) (_, ms2) = mulEqIntersect ms1 ms2

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

countVarsInMultiSet :: MultiSet Term -> MultiSet Term
countVarsInMultiSet ts = MultiSet.concatMap varsOfTerm ts

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
countOccurences :: MultiSet Term -> Int -> Term -> Int
countOccurences occMultSet allOcc currTerm = allOcc - (MultiSet.occur currTerm occMultSet)

lowerCounter :: MultiSet Term -> (Int, Multiequation) -> (Int, Multiequation)
lowerCounter occMultSet (count, (s, m)) = (Set.foldl (countOccurences occMultSet) count s, (s, m))

removeMulEquation :: SortedList (Int, Multiequation) -> ((Int, Multiequation), SortedList (Int, Multiequation))
removeMulEquation sl = let deconstructedU = SortedList.uncons sl in
    if isNothing deconstructedU
        then error "empty sorted list not allowed"
        else
            let (fstElem, newU) = fromJust deconstructedU
                (count, (minS, minM)) = fstElem in
                if count /= 0
                    then error "cycle detected"
                    else
                        (fstElem, SortedList.map (lowerCounter (countVarsInMultiSet minM)) newU)

-- TODO: not sure if it is as simple as just an addition of counts
combineMulEquation :: (Int, Multiequation) -> (Int, Multiequation) -> (Int, Multiequation)
combineMulEquation (count1, (s1, m1)) (count2, (s2, m2)) = (count1 + count2, (Set.union s1 s2, MultiSet.union m1 m2))

combineMulEquations :: (Foldable f) => f (Int, Multiequation) -> (Int, Multiequation)
combineMulEquations mulEqToCombine = foldl combineMulEquation (0, (Set.empty, MultiSet.empty)) mulEqToCombine

accumulateVisitableVarsInUS :: Set Term -> Set (Set Term) -> (Int, Multiequation) -> Set (Set Term)
accumulateVisitableVarsInUS currVertex currAccResult (_, (s, _)) = if (not . Set.disjoint currVertex) s 
    then Set.insert s currAccResult
    else currAccResult

getAllReachableVars :: SortedList (Int, Multiequation) -> Set (Set Term) -> Set Term -> Set (Set Term)
getAllReachableVars allVertices visitedVertices currVertex = let visitableVertices = foldl (accumulateVisitableVarsInUS currVertex) Set.empty allVertices
                                                                 toVisitVertices = Set.difference visitableVertices visitedVertices
                                                                 newVisited = Set.union toVisitVertices visitedVertices in
    foldl (getAllReachableVars allVertices) newVisited toVisitVertices

-- Since multiequation reduction adds to the Z only F (S=C will not be compactified due to [0] S)
-- compactification :: (Foldable f) => f (Int, Multiequation) -> SortedList (Int, Multiequation)
-- compactification sl = let deconstructedUNPR = SortedList.uncons sl in
--     if isNothing deconstructedUNPR
--         -- this will do something else
--         then sl
--         else
--             let ((count, (s, m)), restSL) = fromJust deconstructedUNPR
--                 allIntersectingSets = getAllReachableVars restSL (Set.singleton s) s
--                 lol = SortedList.map restSL
--                 compactS = Set.unions allIntersectingSets in
--                     sl
-- TODO finish

mergeByVariable :: Term -> SortedList (Int, Multiequation) -> SortedList (Int, Multiequation)
mergeByVariable (Var x) me = let (with_var, without_var) = SortedList.partition (\(occ , (l, _)) -> Set.member (Var x) l) me in
    SortedList.union without_var ((SortedList.singleton . combineMulEquations) with_var)
mergeByVariable _ _ = error "Only vars allowed"

-- compactification :: SortedList (Int, Multiequation) -> (Multiequation, SortedList (Int, Multiequation))
-- compactification sl = 


selectMulEquation :: SortedList (Int, Multiequation) -> (Int, Multiequation)
selectMulEquation sl = let deconstructedU = SortedList.uncons sl in
    if isNothing deconstructedU
        then error "empty sorted list not allowed"
        else
            let (fstElem, newU) = fromJust deconstructedU
                (count, (minS, minM)) = fstElem in
                    if count /= 0
                        then error "cycle detected"
                        else fstElem

-- How to input these in Coq? Using inductive proposition?

-- Assumptions:
-- * input is a valid R system
-- * inputted R system has unifier
-- * R corresponds to some set of equations SE (always holds)
-- Conclusions:
-- * outputted R' system is valid
-- * outputted R' system has unifier (this should be obvious if the following conclusion is proved)
-- * outputted R' corresponds to SE, thus R and R' are equivalent
unificationAlgorithmStep :: ([Multiequation], SortedList (Int, Multiequation)) -> ([Multiequation], SortedList (Int, Multiequation))
unificationAlgorithmStep (t, u) = let deconstructedU = SortedList.uncons u in
    if isNothing deconstructedU
        then error "empty sorted list not allowed"
        else
            let (fstElem, newU) = fromJust deconstructedU
                (count, (minS, minM)) = fstElem in
                if count /= 0
                    then error "cycle detected"
                    else
                        let 
                            decrementedNewU = SortedList.map (lowerCounter (countVarsInMultiSet minM)) newU in
                            (t ++ [], decrementedNewU)
                        

-- equationTransfer :: SortedList (Int, Multiequation) -> SortedList (Int, Multiequation)

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
