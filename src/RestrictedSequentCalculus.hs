{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}


--------------------------------------------------------------------------------
-- Preamble
--------------------------------------------------------------------------------

module RestrictedSequentCalculus where

import           Control.Arrow               ((&&&))
import           Control.Comonad.Store       (peeks, pos)
import           Control.Lens
import           Control.Monad               (guard)
import           Data.List                   (intersect, intersperse, (\\))
import           Data.Monoid                 (Endo (..))
import qualified Data.Set                    as S
import           Data.Tree                   (Tree (..), drawTree, flatten,
                                              unfoldTree)

import           Data.Text                   (pack)
import           Text.LaTeX                  hiding (Bottom, Top)
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Packages.AMSMath hiding (to)
-- import Data.Monoid (msum)

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

--------------------------------------------------------------------------------
-- LaTeX display of proofs
--------------------------------------------------------------------------------

preamble :: LaTeX
preamble = documentclass [FontSize $ Pt 12] "article"
         <> usepackage [] "amssymb"
         <> usepackage [] "latexsym"
         <> usepackage [] "bussproofs"

outputLatex :: Judgement -> IO ()
outputLatex j = renderFile "here.tex" (preamble <> uuu j)

uuu :: Judgement -> LaTeX
uuu j = let (Just prf) = prove j
        in document $ toLaTeX prf

translate "∧R"  = raw "$\\wedge R$"
translate "∧L"  = raw "$\\wedge L$"
translate "∨R1" = raw "$\\vee R1$"
translate "∨R2" = raw "$\\vee R2$"
translate "∨L"  = raw "$\\vee L$"
translate "⊃R"  = raw "$\\subset\\!R$"
translate "⊃L"  = raw "$\\subset\\!L$"
translate "⊤R"  = raw "$\\top R$"
translate "⊤L"  = raw "$\\top L$"
translate "⊥L"  = raw "$\\bot L$"
translate "init" = raw "$init$"

inference :: Int -> Judgement -> LaTeX
inference 1 j = comm1 "UnaryInfC"      (toLaTeX j)
inference 2 j = comm1 "BinaryInfC"     (toLaTeX j)
inference 3 j = comm1 "TrinaryInfC"    (toLaTeX j)
inference 4 j = comm1 "QuaternaryInfC" (toLaTeX j)
inference 5 j = comm1 "QuinaryInfC"    (toLaTeX j)

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
    where render p = case p of
            Node  Verified         _  -> comm0 "AxiomC"
            Node (Unexamined    j) js -> comm1 "AxiomC" "what"
            Node (Examined desc j) js -> mconcat $
              [ mconcat . map render $ js
              , comm1 "RightLabel" (scriptsize $ translate desc)
              , inference (length js) j ]
