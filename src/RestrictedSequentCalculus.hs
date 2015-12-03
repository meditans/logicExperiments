{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

module RestrictedSequentCalculus where

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
                           , _rightCtx :: Proposition
                           } deriving (Eq)
makeLenses ''Judgement

instance Show Judgement where
  show (Judgement l r) = show (S.toList l) ++ " ⇒ " ++ show r


--------------------------------------------------------- Proof and Search Trees

type RuleDescription = String

data Examined a = Unexamined a | Examined RuleDescription a | Verified deriving (Eq)
makePrisms ''Examined

instance (Show a) => Show (Examined a) where
  show (Unexamined e)    = "Unexamined: " ++ show e
  show (Examined name e) = show e ++ "       (" ++ name ++ ")"
  show Verified          = "Verified"

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
  (a,b) <- j ^.. rightCtx . (.:∧)
  return . buildDerivationStep "∧R" j $ do
    x <- [a,b]
    return . (rightCtx .~ x) $ j)

orL :: Rule
orL =  Rule "∨L" (\j -> do
  (a,b) <- j ^.. leftCtx . folded . (.:∨)
  return . buildDerivationStep "∨L" j $ do
    x <- [a,b]
    return . (leftCtx . contains (a :∨ b) .~ False)
           . (leftCtx . contains x         .~ True) $ j)

orR1 :: Rule
orR1 =  Rule "∨R1" (\j -> do
  (a,b) <- j ^.. rightCtx . (.:∨)
  return . buildDerivationStep "∨R1" j . singleton
         . (rightCtx .~ a) $ j)

orR2 :: Rule
orR2 =  Rule "∨R2" (\j -> do
  (a,b) <- j ^.. rightCtx . (.:∨)
  return . buildDerivationStep "∨R2" j . singleton
         . (rightCtx .~ b) $ j)

implicationL :: Rule
implicationL = Rule "⊃L" (\j -> do
  (a,b) <- j ^.. leftCtx  . folded . (.:⊃)
  c     <- j ^.. rightCtx
  return . buildDerivationStep "⊃L" j $
    [ (rightCtx .~ a) $ j
    , (leftCtx  . contains b .~ True) . (leftCtx . contains (a :⊃ b) .~ False) $ j ])

implicationR :: Rule
implicationR = Rule "⊃R" (\j -> do
  (a,b) <- j ^.. rightCtx . (.:⊃)
  return . buildDerivationStep "⊃R" j . singleton
         . (leftCtx  . contains a .~ True)
         . (rightCtx .~ b) $ j)

truthL :: Rule
truthL = Rule "⊤L" (\j -> do
  guard (j ^. leftCtx . contains Top == True)
  return . buildDerivationStep "⊤L" j . singleton
         . (leftCtx . contains Top .~ False) $ j)

truthR :: Rule
truthR = Rule "⊤R" (\j -> do
  guard (j ^. rightCtx == Top)
  return $ Node (Examined "⊤R" j) [Node Verified []])

falsehoodL :: Rule
falsehoodL = Rule "⊥L" (\j -> do
  guard (j ^. leftCtx . contains Bottom)
  return $ Node (Examined "⊥L" j) [Node Verified []])

initRule :: Rule
initRule =  Rule "init" (\j -> do
  guard  $ (j^.rightCtx) `S.member` (j^.leftCtx)
  return $ Node (Examined "init" j) [Node Verified []])

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

isVerifiedTree :: ProofTree -> Bool
isVerifiedTree (Node Verified _) = True
isVerifiedTree _                 = False

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
  return . not . isUnexaminedTree $ pos ctx

prove :: Judgement -> Maybe ProofTree
prove j = j ^? to generateSearchTree . to flatten . traversed . filtered isCompleteProof

--------------------------------------------------------------------------------
-- Simple drawing utilities
--------------------------------------------------------------------------------

drawSearchTree :: SearchTree -> IO ()
drawSearchTree = putStrLn . drawTree . fmap drawProofTree
  where drawProofTree = unlines . map (\xs -> ">>> " ++ xs)
                      . lines . drawTree . fmap show

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
jud = Judgement (S.fromList []) ((Atom "A" :∧ Atom "B") :⊃ (Atom "B" :∧ Atom "A"))

tryImplicationLeft :: Judgement
tryImplicationLeft = Judgement (S.fromList [Atom "A" :⊃ Atom "B"])
                               (Atom "C")

tryImplicationRight :: Judgement
tryImplicationRight = Judgement (S.empty)
                                (Atom "A" :⊃ Atom "B")

tryOrLeft :: Judgement
tryOrLeft = Judgement (S.fromList [Atom "A" :∨ Atom "B"])
                      (Atom "C")

tryOrRight :: Judgement
tryOrRight = Judgement (S.empty)
                       (Atom "A" :∨ Atom "B")

tryTruthLeft :: Judgement
tryTruthLeft = Judgement (S.fromList [Top]) (Atom "A")

tryTruthRight :: Judgement
tryTruthRight = Judgement (S.empty) (Top)

tryFalsehoodLeft :: Judgement
tryFalsehoodLeft = Judgement (S.fromList [Atom "A", Bottom]) (Atom "B")
