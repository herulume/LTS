{-# LANGUAGE FlexibleInstances #-}
module Adventurers where

import DurationMonad
import Data.List (tails)
import Data.Monoid
import Control.Monad (mapM_)

-- The list of adventurers
data Adventurer = P1 | P2 | P5 | P10 deriving (Show,Eq)
-- Adventurers + the lantern
type Objects = Either Adventurer ()

-- The time that each adventurer needs to cross the bridge
-- To implement
getTimeAdv :: Adventurer -> Int
getTimeAdv P1 = 1
getTimeAdv P2 = 2
getTimeAdv P5 = 5
getTimeAdv P10 = 10

{-- The state of the game, i.e. the current position of each adventurer
+ the lantern. The function (const False) represents the initial state
of the game, with all adventurers and the lantern on the left side of
the bridge. Similarly, the function (const True) represents the end
state of the game, with all adventurers and the lantern on the right
side of the bridge.  --}
type State = Objects -> Bool

instance Show State where
  show s = (show . (fmap show)) [s (Left P1),
                                 s (Left P2),
                                 s (Left P5),
                                 s (Left P10),
                                 s (Right ())]

instance Eq State where
  (==) s1 s2 = and [s1 (Left P1) == s2 (Left P1),
                    s1 (Left P2) == s2 (Left P2),
                    s1 (Left P5) == s2 (Left P5),
                    s1 (Left P10) == s2 (Left P10),
                    s1 (Right ()) == s2 (Right ())]



-- The initial state of the game
gInit :: State
gInit = const False

-- Changes the state of the game for a given object
changeState :: Objects -> State -> State
changeState a s = let v = s a in (\x -> if x == a then not v else s x)

-- Changes the state of the game of a list of objects
mChangeState :: [Objects] -> State -> State
mChangeState os s = foldr changeState s os


{-- For a given state of the game, the function presents all the
possible moves that the adventurers can make.  --}
-- To implement
allValidPlays :: State -> ListDur State
allValidPlays s =
    let fLSide  = s . Right $ ()
        valid   = foldr (\p a -> if fLSide == s (Left p) then p:a else a) [] [P1, P2, P5, P10]
        pairs l = [(x,y) | (x:ys) <- tails l, y <- x:ys]
     in LD $ do
         (p', p'') <- pairs valid
         if p' == p'' then  return $ Duration (getTimeAdv p', mChangeState [Left p', Right ()] s)
                      else  return $ Duration ( max (getTimeAdv p') (getTimeAdv p'')
                                              , mChangeState [Left p', Left p'', Right ()] s
                                              )

{-- For a given number n and initial state, the function calculates
all possible n-sequences of moves that the adventures can make --}
-- To implement
exec :: Int -> State -> ListDur State
exec 0 _ = LD []
exec 1 s = allValidPlays s
exec n s = allValidPlays s >>= exec (n-1)

{-- Is it possible for all adventurers to be on the other side
in <=17 min and not exceeding 5 moves ? --}
-- To implement
leq17 :: Bool
leq17 = allSafeAnd (<=17)

{-- Is it possible for all adventurers to be on the other side
in < 17 min ? --}
-- To implement
l17 :: Bool
l17 = allSafeAnd (< 17)

{-- Is it possible for any adventurers to be on the other side
in < their ? --}
anyLTheirTime :: Bool
anyLTheirTime = any (\x -> any (\(p', s) -> either ((s &&) . (getDuration x <) . getTimeAdv) (const False) p') (getValue x)) baseQuery


{-- Must pass with flashlight
--}
withFlashlight :: Bool
withFlashlight = all check . fmap (\(Duration (_, l)) -> l) . remLD $ exec 5 gInit where
    check :: State -> Bool
    check s = let os = [Left P1, Left P2, Left P5, Left P10]
                  fl = Right ()
                  actual = fmap s os
                  next = fmap (\(Duration (_, l)) -> (l, fmap l os)) . remLD . allValidPlays $ s
                  diff = fmap (fmap (getAny . foldMap Any . zipWith (==) actual)) next
                in foldr (\(f, b) acc-> not b || (((f fl) /= (s fl)) && acc)) True diff

allSafeAnd :: (Int -> Bool) -> Bool
allSafeAnd f = any (\x -> all (==True) (fmap snd (getValue x)) && f (getDuration x)) baseQuery

baseQuery :: [Duration [(Objects, Bool)]]
baseQuery = remLD . fmap (\s -> fmap (\p -> (p, s p)) [Left P1, Left P2, Left P5, Left P10, Right ()]) $ exec 5 gInit

allQueries :: IO ()
allQueries = mapM_ putStrLn
    [ "Is it possible for all adventurers to be on the other side in <=17 min and not exceeding 5 moves?"
    , show leq17 <> "\n"
    , "Is it possible for all adventurers to be on the other side in < 17 min and not exceeding 5 moves?"
    , show l17 <> "\n"
    , "Is it possible for any adventurers to be on the other side in < their time ?"
    , show anyLTheirTime <> "\n"
    , "They must always pass with the flashlight"
    ,  show withFlashlight
    ]
--------------------------------------------------------------------------
{-- Implementation of the monad used for the problem of the adventurers.
Recall the Knight's quest --}

data ListDur a = LD [Duration a] deriving Show

remLD :: ListDur a -> [Duration a]
remLD (LD x) = x

-- To implement
instance Functor ListDur where
   fmap f =  LD . fmap (fmap f) . remLD

-- To implement
instance Applicative ListDur where
   pure = LD . pure . pure
   l1 <*> l2 = LD $ do
       df <- remLD l1
       dv <- remLD l2
       return $ df <*> dv

-- To implement
instance Monad ListDur where
   return = pure
   l >>= k = LD $ remLD l >>= (\(Duration (s, x)) ->
        fmap (\(Duration (s', z)) -> Duration (s + s', z)) (remLD (k x)))

manyChoice :: [ListDur a] -> ListDur a
manyChoice = LD . concat . (map remLD)
--------------------------------------------------------------------------
{-- Extra
Here be dragons. And monads. --}

newtype ListDurLog w a = LDL [(w, Duration a)] deriving Show

remLDL :: ListDurLog w a -> [(w, Duration a)]
remLDL (LDL x) = x

instance Functor (ListDurLog w) where
   fmap f = LDL . fmap (fmap (fmap f)) . remLDL

instance Monoid w => Applicative (ListDurLog w) where
   pure x = LDL . pure $ (mempty, pure x)
   l1 <*> l2 = LDL $ do
        (w, df) <- remLDL l1
        (w', f) <- remLDL l2
        pure (w <> w', df <*> f)

instance Monoid w => Monad (ListDurLog w) where
   return = pure
   l >>= k = LDL $ remLDL l >>= (\(w, (Duration (s, x))) ->
        fmap (\(w', (Duration (s', z))) -> (w <> w', Duration (s + s', z))) (remLDL (k x)))

