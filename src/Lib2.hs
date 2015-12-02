{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}


-- Preamble

{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
module Lib2 where

import Data.Tree
import Data.Tree.Lens
import Control.Lens
import Control.Comonad.Store
import Data.Monoid (Endo (..))


-- Data Types

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
-- for a classical logic sequent calculus (for the intuitionistic one a
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


-- Rules

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

rules = [andR, andL]

completelyApplyRule :: Rule -> Judgement -> [[Judgement]]
completelyApplyRule r j = map (applyLocally r j) (findLoci r j)

completelyApplyRule' :: Rule -> ProofTree -> [ProofTree]
completelyApplyRule' r (Node (Unexamined j) []) = map constructTree (findLoci r j)
  where constructTree = Node (Examined (name r) j) . map (\x -> Node (Unexamined x) []) . applyLocally r j
completelyApplyRule' _ x = []

applyAllRules :: ProofTree -> [ProofTree]
applyAllRules p = concatMap (\r -> completelyApplyRule' r p) rules


-- Helper functions for rules

substituteAt :: Int -> (a -> [a]) -> [a] -> [a]
substituteAt i f xs = take i xs ++ f (xs!!i) ++ drop (i+1) xs

distributeAt :: Int -> (a -> [a]) -> [a] -> [[a]]
distributeAt i f xs = zipWith substitute variations (repeat xs)
  where substitute a c = ix i .~ a $ c
        variations = f (xs !! i)

-- Difficult part

-- Questa funzione mi consente di applicare una funzione alle foglie degli
-- alberi, in maniera da espanderle
-- finally = map (peeks foo) $ filter (isUnexaminedTree . pos) $ contexts tree

-- nel mio caso sarebbe un:
isUnexaminedTree :: ProofTree -> Bool
isUnexaminedTree (Node (Unexamined _) _) = True
isUnexaminedTree _                       = False

-- Ho bisogno di
-- foo :: Proposition -> [Proposition] WHAT

-- Ovvero una funzione che applichi tutte le regole. Questa cosa puo' essere
-- facilmente decomposta in una funzione che applichi una sola regola in tutti i
-- posti possibili, e questa e' facile da scrivere

-- Questa funzione ritorna una lista di possibilita', WHAT. Il problema e' che i
-- due livelli di lista parlano di due cose diverse, perche' uno parla del fatto
-- che ci sono diverse possibilita', e questo va rappresentato con diversi rami
-- nell'albero delle prove, mentre l'altro dice che ci possono essere tante
-- premesse, cose che sono rami nell'albero della derivazione.

-- Risolverebbe il problema una cosa come:
-- again :: Rule -> Judgement -> [ProofTree]

-- secondo me lo risolverebbe, perche' a quel punto potrei semplicemente
-- astrarre sulle regole mettendo tutto assieme, e ottenere qualcosa nella
-- forma:
-- Judgement -> [ProofTree]
-- Che non e' molto diverso direttamente da
-- ProofTree -> [ProofTree]
-- Assumendo che l'albero cominci con una struttura di unexplored. A quel punto avrei quanto mi serve per generare

-- come vediamo ho ancora bisogno di qualcosina in piu', visto che nella
-- struttura che mi sto pensando questa cosa dovrebbe avere tipo ProofTree ->
-- ProofTree

vediamo :: (ProofTree -> [ProofTree]) -> ProofTree -> [ProofTree]
vediamo f p = concat $ do
  x <- f p
  return . map (peeks $ const x) . filter (isUnexaminedTree . pos) $ contexts p

-- unfoldTree :: (b -> (a, [b])) -> b -> Tree a
-- unfoldTree :: (ProofTree -> (ProofTree, [ProofTree])) -> ProofTree -> Tree ProofTree
generate :: Judgement -> SearchTree
generate j = unfoldTree (\p -> (p, vediamo applyAllRules p)) (Node (Unexamined j) [])

drawProofTree :: (Show a) => Tree a -> String
drawProofTree = unlines . map (\xs -> ">>> " ++ xs) . lines . drawTree . fmap show

drawSearchTree :: SearchTree -> IO ()
drawSearchTree = putStrLn . drawTree . fmap drawProofTree



-- contesti, proposizioni, ed esempi vari
jud = Judgement [Atom "A" :∧ Atom "B", Atom "C"] [Atom "B" :∧ Atom "A"]

exPrfTree = Node (Unexamined jud) []

exPrfTree2 :: ProofTree
exPrfTree2 = Node (Examined "∧R" (Judgement [] [(Atom "A" :∧ Atom "B")]))
                  [ Node (Unexamined (Judgement [] [(Atom "A")])) []
                  , Node (Unexamined (Judgement [] [(Atom "B")])) [] ]
