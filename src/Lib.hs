{-# LANGUAGE TypeFamilies #-}
module Lib where

import Data.Tree
import Control.Lens
import Control.Arrow ((&&&))

data Judgement = [Proposition] :⇒ [Proposition] deriving (Eq, Show)

data Proposition = Atom Char
                 | Proposition :∧ Proposition
                 | Proposition :⊃ Proposition
                 deriving (Eq, Show)

isConj (p1 :∧ p2) = True
isConj _ = False

ando :: Proposition -> Proposition -> Proposition
ando x y = x :∧ y

clampAt :: Int -> Tree a -> Tree a
clampAt 0 (Node root _)        = Node root []
clampAt n (Node root children) = Node root $ map (clampAt (n-1)) children

draw :: (Show a) => Tree a -> IO ()
draw = putStrLn . drawTree . fmap show . clampAt 3

-- andRloc è pensato per scindere localmente una and nella parte destra di un
-- giudizio, una volta dato l'indice dove la cosa succede. Unsafe

allRules :: Judgement -> [Judgement]
allRules j = andR j ++ andL j

andRloc :: Judgement -> Int -> [Judgement]
andRloc (ls :⇒ rs) i = map (ls :⇒) $ distributingAt rs (\(p1 :∧ p2) -> [p1,p2]) i

andR :: Judgement -> [Judgement]
andR j@(_ :⇒ rs) = concatMap (andRloc j) (rs^..traversed.filtered isConj.asIndex)

andLloc :: Judgement -> Int -> Judgement
andLloc (ls :⇒ rs) i = substitutingAt ls (\(p1 :∧ p2) -> [p1,p2]) i :⇒ rs

andL :: Judgement -> [Judgement]
andL j@(ls :⇒ _) = map (andLloc j) (ls^..traversed.filtered isConj.asIndex)

substitutingAt :: [a] -> (a -> [a]) -> Int -> [a]
substitutingAt xs f i = take i xs ++ f (xs!!i) ++ drop (i+1) xs

distributingAt :: [a] -> (a -> [a]) -> Int -> [[a]]
distributingAt xs f i = zipWith subst (f $ xs!!i) (repeat xs)
  where subst a = iix i .~ a

example = draw $ unfoldTree (id &&& andR) ([] :⇒ [Atom 'a' :∧ Atom 'b'])
