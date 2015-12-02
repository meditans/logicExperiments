{-# LANGUAGE TemplateHaskell, TypeFamilies #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

module Lib2 where

import           Control.Comonad.Store
import           Control.Lens
import           Control.Monad         (guard)
import           Data.List             (intersect, (\\))
import           Data.Monoid           (Endo (..))
import           Data.Tree
import           Data.Tree.Lens

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

data Proposition = Atom String
                 | Proposition :∧ Proposition
                 | Proposition :⊃ Proposition
                 | Top
                 | Bottom
                 deriving (Eq)
makePrisms ''Proposition

instance Show Proposition where
  show (Atom p) = p
  show (p1 :∧ p2) = show p1 ++ " ∧ " ++ show p2
  show (p1 :⊃ p2) = show p1 ++ " ⊃ " ++ show p2
  show Top = ""

-- I mantain a list of proposition on either side to leave open the possibility
-- for a classical logic sequent calculus (for the intuitionistic one a single
-- proposition would suffice).
data Judgement = Judgement { _leftCtx  :: [Proposition]
                           , _rightCtx :: [Proposition]
                           } deriving (Eq)
makeLenses ''Judgement

instance Show Judgement where
  show (Judgement l r) = show l ++ " ⇒ " ++ show r

type RuleDescription = String

data Examined a = Unexamined a | Examined RuleDescription a deriving (Eq)
makePrisms ''Examined

instance (Show a) => Show (Examined a) where
  show (Unexamined e)     = "Unexamined: " ++ show e
  show (Examined name e) = show e ++ "       (" ++ name ++ ")"

type ProofTree  = Tree (Examined Judgement)
type SearchTree = Tree ProofTree

--------------------------------------------------------------------------------
-- Rules
--------------------------------------------------------------------------------

-- A questo punto, una regola non e' altro che, un traversal che mi fa vedere
-- dove va bene, e l'attuale funzione che calcola, dato un posto locale, la
-- successiva derivazione.

data Rule = Rule { name         :: RuleDescription
                 , findLoci     :: Judgement -> [Int]
                 , applyLocally :: Judgement -> Int -> [Judgement]
                 }

andL :: Rule
andL =  Rule "∧L"
        (\j -> j ^.. leftCtx . itraversed . (.:∧) . asIndex)
        (\j i -> [leftCtx %~ substituteAt i (\(p1 :∧ p2) -> [p1,p2]) $ j])

andR :: Rule
andR =  Rule "∧R"
        (\j -> j ^.. rightCtx . itraversed . (.:∧) . asIndex)
        (\j i -> map (\ps -> Judgement (j^.leftCtx) ps) $ distributeAt i (\(p1 :∧ p2) -> [p1,p2]) (j ^. rightCtx))

initRule :: Rule
initRule =  Rule "init"
        (\j -> if null $ intersect (j^.rightCtx) (j^.leftCtx) then [] else [0])
        (\j _ -> let inters = intersect (j^.rightCtx) (j^.leftCtx)
                 in [(rightCtx %~ (\\inters)) . (leftCtx %~ (\\inters)) $ j])

rules = [andR, andL, initRule]

completelyApplyRule :: Rule -> ProofTree -> [ProofTree]
completelyApplyRule r (Node (Unexamined j) []) = map constructTree (findLoci r j)
  where constructTree = Node (Examined (name r) j) . map (\x -> Node (Unexamined x) []) . applyLocally r j
completelyApplyRule _ x = []

applyAllRules :: ProofTree -> [ProofTree]
applyAllRules p = concatMap (\r -> completelyApplyRule r p) rules

--------------------------------------------------------------------------------
-- Helper functions for rules
--------------------------------------------------------------------------------

substituteAt :: Int -> (a -> [a]) -> [a] -> [a]
substituteAt i f xs = take i xs ++ f (xs!!i) ++ drop (i+1) xs

distributeAt :: Int -> (a -> [a]) -> [a] -> [[a]]
distributeAt i f xs = zipWith substitute variations (repeat xs)
  where substitute a c = ix i .~ a $ c
        variations = f (xs !! i)

--------------------------------------------------------------------------------
-- Difficult part
--------------------------------------------------------------------------------

isUnexaminedTree :: ProofTree -> Bool
isUnexaminedTree (Node (Unexamined _) _) = True
isUnexaminedTree _                       = False

-- Se do una funzione che dato un proofTree mi restituisce le sue possibili
-- derivazioni, ottengo una funzione che applica una sola volta una funzione
-- alle foglie.
distributeUponLeaves :: (ProofTree -> [ProofTree]) -> ProofTree -> [ProofTree]
distributeUponLeaves f p = do
  ctx    <- contexts p
  guard  $ isUnexaminedTree (pos ctx)
  newFoc <- f (pos ctx)
  return $ peeks (const newFoc) ctx

-- Starting from a Judgement, this function generates all the search tree.
generateSearchTree :: Judgement -> SearchTree
generateSearchTree j = unfoldTree (\p -> (p, distributeUponLeaves applyAllRules p)) (Node (Unexamined j) [])

-- Simple drawing utilities, mostly for debugging.
drawProofTree :: (Show a) => Tree a -> String
drawProofTree = unlines . map (\xs -> ">>> " ++ xs) . lines . drawTree . fmap show

drawSearchTree :: SearchTree -> IO ()
drawSearchTree = putStrLn . drawTree . fmap drawProofTree

--------------------------------------------------------------------------------
-- Contesti, proposizioni, ed esempi vari
--------------------------------------------------------------------------------

jud = Judgement [Atom "A" :∧ Atom "B", Atom "C"] [Atom "B" :∧ Atom "A"]

exPrfTree = Node (Unexamined jud) []

exPrfTree2 :: ProofTree
exPrfTree2 = Node (Examined "∧R" (Judgement [] [(Atom "A" :∧ Atom "B")]))
                  [ Node (Unexamined (Judgement [] [(Atom "A")])) []
                  , Node (Unexamined (Judgement [] [(Atom "B")])) [] ]
