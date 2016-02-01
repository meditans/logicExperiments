{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}

--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

module RestrictedSequentCalculus where

import           Control.Arrow                ((&&&))
import           Control.Comonad.Store        (peek, peeks, pos)
import           Control.Lens
import           Control.Monad                (guard)
import           Data.List                    (intersect, intersperse, (\\))
import           Data.Monoid                  (Endo (..))
import qualified Data.Set                     as S
import           Data.Text                    (pack)
import           Data.Tree                    (Tree (..), drawTree, flatten,
                                               unfoldTree)
import           Text.LaTeX                   hiding (Bottom, Top)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Packages.AMSMath  hiding (to)
import           Text.LaTeX.Packages.Geometry

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

data Judgement = Judgement { _leftCtx  :: S.Set Proposition
                           , _rightCtx :: Proposition
                           } deriving (Eq)
makeLenses ''Judgement

instance Show Judgement where
  show (Judgement l r) = show (S.toList l) ++ " ⇒ " ++ show r

--------------------------------------------------------- Proof and Search Trees

data RuleDescription = RuleDescription { ruleName  :: String
                                       , ruleLaTeX :: LaTeX
                                       } deriving (Eq, Show)

data Examined a = Unexamined a
                | Examined RuleDescription a
                | Verified deriving (Eq)
makePrisms ''Examined

instance (Show a) => Show (Examined a) where
  show (Unexamined e)    = "Unexamined: " ++ show e
  show (Examined desc e) = show e ++ "       (" ++ ruleName desc ++ ")"
  show Verified          = "Verified"

type ProofTree  = Tree (Examined Judgement)
type SearchTree = Tree ProofTree

-- | Given the description of a rule, a judgement j, and a list of judgement
--   that derive from j, builds the corresponding ProofTree.
buildDerivationStep :: RuleDescription -> Judgement -> [Judgement] -> ProofTree
buildDerivationStep n jdg jdgs = Node (Examined n jdg) (map toTree jdgs)
  where toTree j = Node (Unexamined j) []

--------------------------------------------------------------------------------
-- Rules
--------------------------------------------------------------------------------

data Rule = Rule { description :: RuleDescription
                 , applyRule   :: Judgement -> [ProofTree] }

andL :: Rule
andL =  Rule desc (\j -> do
  (a,b) <- j ^.. leftCtx . folded . (.:∧)
  return . buildDerivationStep desc j . singleton
    . (leftCtx . contains (a :∧ b) .~ False)
    . (leftCtx . contains a         .~ True)
    . (leftCtx . contains b         .~ True) $ j)
  where desc = (RuleDescription "∧L" (comm0 "wedge" <> "L"))

andR :: Rule
andR =  Rule desc (\j -> do
  (a,b) <- j ^.. rightCtx . (.:∧)
  return . buildDerivationStep desc j $ do
    x <- [a,b]
    return . (rightCtx .~ x) $ j)
  where desc = RuleDescription "∧R" (comm0 "wedge" <> "R")

orL :: Rule
orL =  Rule desc (\j -> do
  (a,b) <- j ^.. leftCtx . folded . (.:∨)
  return . buildDerivationStep desc j $ do
    x <- [a,b]
    return . (leftCtx . contains (a :∨ b) .~ False)
           . (leftCtx . contains x         .~ True) $ j)
  where desc = RuleDescription "∨L" (comm0 "vee" <> "L")

orR1 :: Rule
orR1 =  Rule desc (\j -> do
  (a,b) <- j ^.. rightCtx . (.:∨)
  return . buildDerivationStep desc j . singleton
         . (rightCtx .~ a) $ j)
  where desc = RuleDescription "∨R1" (comm0 "vee" <> "R1")

orR2 :: Rule
orR2 =  Rule desc (\j -> do
  (a,b) <- j ^.. rightCtx . (.:∨)
  return . buildDerivationStep desc j . singleton
         . (rightCtx .~ b) $ j)
  where desc = RuleDescription "∨R2" (comm0 "vee" <> "R2")

implicationL :: Rule
implicationL = Rule desc (\j -> do
  (a,b) <- j ^.. leftCtx  . folded . (.:⊃)
  c     <- j ^.. rightCtx
  return . buildDerivationStep desc j $
    [ (rightCtx .~ a) $ j
    , (leftCtx  . contains b .~ True)
    . (leftCtx . contains (a :⊃ b) .~ False) $ j ])
  where desc = RuleDescription "⊃L"
               (comm0 "supset" <> comm0 "!" <> comm0 "!" <> "L")

implicationR :: Rule
implicationR = Rule desc (\j -> do
  (a,b) <- j ^.. rightCtx . (.:⊃)
  return . buildDerivationStep desc j . singleton
         . (leftCtx  . contains a .~ True)
         . (rightCtx .~ b) $ j)
  where desc = RuleDescription "⊃R"
               (comm0 "supset" <> comm0 "!" <> comm0 "!" <> "R")

truthL :: Rule
truthL = Rule desc (\j -> do
  guard (j ^. leftCtx . contains Top == True)
  return . buildDerivationStep desc j . singleton
         . (leftCtx . contains Top .~ False) $ j)
  where desc = RuleDescription "⊤L" (comm0 "top" <> "L")

truthR :: Rule
truthR = Rule desc (\j -> do
  guard (j ^. rightCtx == Top)
  return $ Node (Examined desc j) [Node Verified []])
  where desc = RuleDescription "⊤R" (comm0 "top" <> "R")

falsehoodL :: Rule
falsehoodL = Rule desc (\j -> do
  guard (j ^. leftCtx . contains Bottom)
  return $ Node (Examined desc j) [Node Verified []])
  where desc = RuleDescription "⊥L" (comm0 "bot" <> "L")

initRule :: Rule
initRule =  Rule desc (\j -> do
  guard  $ (j^.rightCtx) `S.member` (j^.leftCtx)
  return $ Node (Examined desc j) [Node Verified []])
  where desc = (RuleDescription "init" "init")

rules :: [Rule]
rules = [initRule, andR, andL, orR1, orR2, orL, implicationR, implicationL, truthR, truthL, falsehoodL]

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

distributeUponLeaves :: (Judgement -> [ProofTree]) -> ProofTree -> [ProofTree]
distributeUponLeaves f p = do
  ctx    <- contexts p
  guard  $ isUnexaminedTree (pos ctx)
  newFoc <- f (rootJudgement . pos $ ctx)
  let newTree = peek newFoc ctx
  guard  $ unencumbered [] newTree
  return newTree
 where
  rootJudgement (Node (Unexamined j) _) = j


generateSearchTree :: Judgement -> SearchTree
generateSearchTree j = unfoldTree (id &&& (distributeUponLeaves applyAllRules))
                                  (Node (Unexamined j) [])

unencumbered :: [Judgement] -> ProofTree -> Bool
unencumbered js (Node Verified _) = True
unencumbered js (Node ej ts) = (unexamine ej `notElem` js)
                            && all (unencumbered (unexamine ej : js)) ts
  where
    unexamine (Unexamined j) = j
    unexamine (Examined _ j) = j

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

jud2 :: Judgement
jud2 = Judgement (S.fromList []) $ ((Atom "A" :∧ Atom "B") :∧ Atom "C")
                               :⊃ (Atom "A" :∧ (Atom "B" :∧ Atom "C"))

jud3 :: Judgement
jud3 = Judgement (S.fromList []) $ (Bottom :⊃ Atom "A")

jud4 :: Judgement
jud4 = Judgement (S.fromList []) $ Atom "A" :⊃ (Atom "B" :⊃ (Atom "A" :∧ Atom "B"))

jud5 :: Judgement
jud5 = Judgement (S.fromList []) $ (Atom "A" :⊃ Atom "C") :⊃
                                   ((Atom "B" :⊃ Atom "C") :⊃
                                   ((Atom "A" :∨ Atom "B") :⊃ Atom "C"))

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

--------------------------------------------------------------------------------
-- LaTeX display of proofs
--------------------------------------------------------------------------------

latexProof :: Judgement -> IO ()
latexProof j = maybe
  (putStrLn "I didn't find a proof.")
  latexProofTree
  (prove j)

latexProofTree :: ProofTree -> IO ()
latexProofTree p = renderFile "proof.tex" $ preamble <> document (toLaTeX p)
  where
    preamble = documentclass [FontSize $ Pt 12] "article"
            <> importGeometry [GPaperHeight (Cm 40), GPaperWidth (Cm 40)]
            <> usepackage [] "amssymb"
            <> usepackage [] "latexsym"
            <> usepackage [] "bussproofs"

--------------------------------------------------------------------------------
-- ToLaTeX typeclass
--------------------------------------------------------------------------------

class ToLaTeX a where
  toLaTeX :: a -> LaTeX

instance ToLaTeX Proposition where
  toLaTeX p = case p of
    Atom x   -> raw (pack x)
    x1 :∧ x2 -> parenthesis $ wedge  (toLaTeX x1) (toLaTeX x2)
    x1 :∨ x2 -> parenthesis $ vee    (toLaTeX x1) (toLaTeX x2)
    x1 :⊃ x2 -> parenthesis $ subset (toLaTeX x1) (toLaTeX x2)
    Top    -> comm0 "top"
    Bottom -> comm0 "bot"
    where parenthesis x = between x "(" ")"

instance ToLaTeX Judgement where
  toLaTeX (Judgement lhs rhs) = (math . mconcat)
    [ (mconcat . intersperse ",") (map toLaTeX (S.toList lhs))
    , comm0 "Longrightarrow"
    , toLaTeX rhs ]

instance ToLaTeX ProofTree where
  toLaTeX p = mconcat
    [ comm1 "begin" "prooftree"
    , render p
    , comm1 "end" "prooftree" ]
    where
      render p = case p of
        Node  Verified         _  -> comm0 "AxiomC"
        Node (Unexamined    j) js -> comm1 "AxiomC" "what"
        Node (Examined desc j) js -> mconcat $
          [ (mconcat . map render) js
          , comm1 "RightLabel" (scriptsize . math $ ruleLaTeX desc)
          , comm1 (inferences js) (toLaTeX j)]
      inferences js = case length js of
        1 -> "UnaryInfC"
        2 -> "BinaryInfC"
        3 -> "TrinaryInfC"
        4 -> "QuaternaryInfC"
        5 -> "QuinaryInfC"
