{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

module Lib2 where

import           Control.Arrow         ((&&&))
import           Control.Comonad.Store (peeks, pos)
import           Control.Lens
import           Control.Monad         (guard)
import           Data.List             (intersect, (\\))
import           Data.Monoid           (Endo (..))
import qualified Data.Set              as S
import           Data.Tree             (Tree (..), drawTree, flatten,
                                        unfoldTree)

--------------------------------------------------------------------------------
-- Data Types
--------------------------------------------------------------------------------

------------------------------------------------------------------- Propositions
data Proposition = Atom String
                 | Proposition :∧ Proposition
                 | Proposition :∨ Proposition
                 | Proposition :⊃ Proposition
                 | Top
                 | Bottom
                 deriving (Eq, Ord)

makePrisms ''Proposition

instance Show Proposition where
  show (Atom p) = p
  show (p1 :∧ p2) = show p1 ++ " ∧ " ++ show p2
  show (p1 :∨ p2) = show p1 ++ " ∨ " ++ show p2
  show (p1 :⊃ p2) = show p1 ++ " ⊃ " ++ show p2
  show Top = "⊤"
  show Bottom = "⊥"

--------------------------------------------------------------------- Judgements

-- I chose to mantain a list of proposition on either side to leave open the
-- possibility for a classical logic sequent calculus (for the intuitionistic
-- one a single proposition would suffice).

data Judgement = Judgement { _leftCtx  :: S.Set Proposition
                           , _rightCtx :: S.Set Proposition
                           } deriving (Eq)
makeLenses ''Judgement

instance Show Judgement where
  show (Judgement l r) = show l ++ " ⇒ " ++ show r


--------------------------------------------------------- Proof and Search Trees

type RuleDescription = String

data Examined a = Unexamined a | Examined RuleDescription a deriving (Eq)
makePrisms ''Examined

instance (Show a) => Show (Examined a) where
  show (Unexamined e)     = "Unexamined: " ++ show e
  show (Examined name e) = show e ++ "       (" ++ name ++ ")"

type ProofTree  = Tree (Examined Judgement)
type SearchTree = Tree ProofTree

buildDerivationStep :: String -> Judgement -> [Judgement] -> ProofTree
buildDerivationStep n jdg jdgs = Node (Examined n jdg) $ map (\j -> Node (Unexamined j) []) jdgs

--------------------------------------------------------------------------------
-- Rules
--------------------------------------------------------------------------------

data Rule = Rule { name      :: RuleDescription
                 , applyRule :: Judgement -> [ProofTree] }

andL :: Rule
andL =  Rule "∧L" (\j -> do
  (a,b) <- j ^.. leftCtx . folded . (.:∧)
  return . buildDerivationStep "∧L" j . singleton
    . (leftCtx . contains (a :∧ b) .~ False)
    . (leftCtx . contains a         .~ True)
    . (leftCtx . contains b         .~ True) $ j)

andR :: Rule
andR =  Rule "∧R" (\j -> do
  (a,b) <- j ^.. rightCtx . folded . (.:∧)
  return . buildDerivationStep "∧R" j $ do
    x <- [a,b]
    return . (rightCtx . contains (a :∧ b) .~ False)
           . (rightCtx . contains x         .~ True) $ j)

orL :: Rule
orL =  Rule "∨L" (\j -> do
  (a,b) <- j ^.. leftCtx . folded . (.:∨)
  return . buildDerivationStep "∨L" j $ do
    x <- [a,b]
    return . (leftCtx . contains (a :∨ b) .~ False)
           . (leftCtx . contains x         .~ True) $ j)

orR1 :: Rule
orR1 =  Rule "∨R1" (\j -> do
  (a,b) <- j ^.. rightCtx . folded . (.:∨)
  return . buildDerivationStep "∨R1" j . singleton
         . (rightCtx . contains (a :∨ b) .~ False)
         . (rightCtx . contains a         .~ True) $ j)

orR2 :: Rule
orR2 =  Rule "∨R2" (\j -> do
  (a,b) <- j ^.. rightCtx . folded . (.:∨)
  return . buildDerivationStep "∨R2" j . singleton
         . (rightCtx . contains (a :∨ b) .~ False)
         . (rightCtx . contains b         .~ True) $ j)

implicationL :: Rule
implicationL = Rule "⊃L" (\j -> do
  (a,b) <- j ^.. leftCtx  . folded . (.:⊃)
  c     <- j ^.. rightCtx . folded
  return . buildDerivationStep "⊃L" j $
    [ (rightCtx . contains a .~ True) . (rightCtx . contains c .~ False) $ j
    , (leftCtx  . contains b .~ True) . (leftCtx . contains (a :⊃ b) .~ False) $ j ])

implicationR :: Rule
implicationR = Rule "⊃R" (\j -> do
  (a,b) <- j ^.. rightCtx . folded . (.:⊃)
  return . buildDerivationStep "⊃R" j . singleton
         . (leftCtx  . contains a .~ True)
         . (rightCtx . contains b .~ True)
         . (rightCtx . contains (a :⊃ b) .~ False) $ j)

truthL :: Rule
truthL = Rule "⊤L" (\j -> do
  return . buildDerivationStep "⊤L" j . singleton
         . (leftCtx . contains Top .~ False) $ j)

truthR :: Rule
truthR = Rule "⊤R" (\j -> do
  guard (j ^. rightCtx . contains Top)
  return . buildDerivationStep "⊤R" j . singleton
         . (rightCtx . contains Top .~ False) $ j)

initRule :: Rule
initRule =  Rule "init" (\j -> do
  let common = (j^.leftCtx) `S.intersection` (j^.rightCtx)
  guard (not $ S.null common)
  return . buildDerivationStep "init" j . singleton
         . (leftCtx  %~ (`S.difference` common))
         . (rightCtx %~ (`S.difference` common))
         $ j)

rules :: [Rule]
rules = [andR, andL, orR1, orR2, orL, implicationR, implicationL, truthR, truthR, initRule]

applyAllRules :: Judgement -> [ProofTree]
applyAllRules p = concatMap (flip applyRule p) rules

--------------------------------------------------------------------------------
-- SearchTree generation
--------------------------------------------------------------------------------

isUnexaminedTree :: ProofTree -> Bool
isUnexaminedTree (Node (Unexamined _) _) = True
isUnexaminedTree _                       = False

rootJudgement :: ProofTree -> Judgement
rootJudgement (Node (Unexamined j) _) = j
rootJudgement (Node (Examined _ j) _) = j

distributeUponLeaves :: (Judgement -> [ProofTree]) -> ProofTree -> [ProofTree]
distributeUponLeaves f p = do
  ctx    <- contexts p
  guard  $ isUnexaminedTree (pos ctx)
  newFoc <- f (rootJudgement . pos $ ctx)
  return $ peeks (const newFoc) ctx

generateSearchTree :: Judgement -> SearchTree
generateSearchTree j = unfoldTree (id &&& (distributeUponLeaves applyAllRules))
                                  (Node (Unexamined j) [])

--------------------------------------------------------------------------------
-- Isolating an actual proof in the SearchTree
--------------------------------------------------------------------------------
isCompleteProof :: ProofTree -> Bool
isCompleteProof p = and $ do
  ctx <- contexts p
  guard $ isUnexaminedTree (pos ctx)
  return $ (pos ctx ^. to rootJudgement . rightCtx) == S.empty

prove :: Judgement -> Maybe ProofTree
prove j = j ^? to generateSearchTree . to flatten . traversed . filtered isCompleteProof

--------------------------------------------------------------------------------
-- Simple drawing utilities
--------------------------------------------------------------------------------

drawProofTree :: (Show a) => Tree a -> String
drawProofTree = unlines . map (\xs -> ">>> " ++ xs) . lines . drawTree . fmap show

drawSearchTree :: SearchTree -> IO ()
drawSearchTree = putStrLn . drawTree . fmap drawProofTree

drawProof :: Judgement -> IO ()
drawProof j = maybe (putStrLn "I didn't found a proof :(")
                    (putStrLn . drawTree . fmap show)
                    (prove j)

--------------------------------------------------------------------------------
-- Utilities, examples, and tests
--------------------------------------------------------------------------------

singleton :: a -> [a]
singleton x = [x]

jud :: Judgement
jud = Judgement (S.fromList [Atom "A" :∧ Atom "B", Atom "C"])
                (S.fromList [Atom "B" :∧ Atom "A"])

jud2 :: Judgement
jud2 = Judgement (S.fromList []) (S.fromList [(Atom "A" :∧ Atom "B") :⊃ (Atom "B" :∧ Atom "A")])

exPrfTree :: ProofTree
exPrfTree = Node (Unexamined jud2) []

tryImplicationLeft :: Judgement
tryImplicationLeft = Judgement (S.fromList [Atom "A" :⊃ Atom "B"])
                               (S.fromList [Atom "C", Atom "D"])

tryImplicationRight :: Judgement
tryImplicationRight = Judgement (S.empty)
                                (S.fromList [Atom "A" :⊃ Atom "B"])

tryOrLeft :: Judgement
tryOrLeft = Judgement (S.fromList [Atom "A" :∨ Atom "B"])
                      (S.empty)

tryOrRight :: Judgement
tryOrRight = Judgement (S.empty)
                       (S.fromList [Atom "A" :∨ Atom "B"])

tryTruthLeft :: Judgement
tryTruthLeft = Judgement (S.fromList [Top]) (S.empty)

tryTruthRight :: Judgement
tryTruthRight = Judgement (S.empty) (S.fromList [Top])
