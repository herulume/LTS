{-# LANGUAGE FlexibleInstances #-}
module Adventurers where

import DurationMonad
import Data.List (tails, intersperse, foldl')
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
         if p' == p'' then return $ Duration (getTimeAdv p', mChangeState [Left p', Right ()] s)
                      else return $ Duration ( max (getTimeAdv p') (getTimeAdv p'')
                                             , mChangeState [Left p', Left p'', Right ()] s
                                             )

{-- For a given number n and initial state, the function calculates all possible n-sequences of moves that the adventures can make --}
-- To implement
exec :: Int -> State -> ListDur State
exec 0 _ = LD []
exec 1 s = allValidPlays s
exec n s = allValidPlays s >>= exec (n-1)

{-- Is it possible for all adventurers to be on the other side in <=17 min and not exceeding 5 moves ? --}
-- To implement
leq17 :: Bool
leq17 = allSafeAnd (<= 17)

{-- Is it possible for all adventurers to be on the other side in < 17 min ? --}
-- To implement
l17 :: Bool
l17 = allSafeAnd (< 17)

{-- Is it possible for any adventurers to be on the other side in < their ? --}
anyLTheirTime :: Bool
anyLTheirTime = any (\x -> any (\(p', s) -> either ((s &&) . (getDuration x <) . getTimeAdv) (const False) p') (getValue x)) baseQuery


{-- Must pass with flashlight --}
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
baseQuery = remLD . fmap (\s -> fmap (\p -> (p, s p)) adv) $ exec 5 gInit

allQueries :: IO ()
allQueries = mapM_ putStrLn
    [ "Is it possible for all adventurers to be on the other side in <=17 minutes and not exceeding 5 moves?"
    , show leq17 <> "\n"
    , "Is it possible for all adventurers to be on the other side in < 17 minutes and not exceeding 5 moves?"
    , show l17 <> "\n"
    , "Is it possible for any adventurers to be on the other side in < their own time?"
    , show anyLTheirTime <> "\n"
    , "Any adventurer must always pass with the flashlight"
    ,  show withFlashlight
    ]
--------------------------------------------------------------------------
data ListDur a = LD [Duration a] deriving Show

remLD :: ListDur a -> [Duration a]
remLD (LD x) = x

instance Functor ListDur where
   fmap f =  LD . fmap (fmap f) . remLD

instance Applicative ListDur where
   pure = LD . pure . pure
   l1 <*> l2 = LD $ do
       df <- remLD l1
       dv <- remLD l2
       return $ df <*> dv

instance Monad ListDur where
   return = pure
   l >>= k = LD $ remLD l >>= (\(Duration (s, x)) ->
        fmap (\(Duration (s', z)) -> Duration (s + s', z)) . remLD . k $ x)

manyChoice :: [ListDur a] -> ListDur a
manyChoice = LD . concat . (map remLD)
--------------------------------------------------------------------------
{-- Extra. Here be dragons. And monads. --}

newtype ListDurLog w a = LDL [(w, Duration a)] deriving Show

remLDL :: ListDurLog w a -> [(w, Duration a)]
remLDL (LDL x) = x

instance Functor (ListDurLog w) where
   fmap f = LDL . fmap (fmap (fmap f)) . remLDL

{-
    Functor's laws

    fmap id = id
    { def }
    LDL . fmap (fmap (fmap id)) . remLDL = id
    { valids fmap }
    LDL . id . remLDL = id
    { LDL . remLDL = id, remove id }
    id = id

    fmap (f . g) ==  fmap f . fmap g
    { fmap def }
    fmap (f . g) == LDL . fmap (fmap (fmap f)) . remLDL . LDL . fmap (fmap (fmap g)) . remLDL
    { LDL . remLDL = id, remove id }
    fmap (f . g) == LDL . fmap (fmap (fmap f)) . fmap (fmap (fmap g)) . remLD
    { fmap (f . g) = fmap f . fmap g x3 }
    fmap (f . g) == LDL . fmap (fmap (fmap f .g)) . remLDL
    { fmap def }
    fmap (f . g) == fmap (f . g)
-}

instance Monoid w => Applicative (ListDurLog w) where
   pure x = LDL . pure $ (mempty, pure x)
   l1 <*> l2 = LDL $ do
        (w, df) <- remLDL l1
        (w', f) <- remLDL l2
        pure (w <> w', df <*> f)

{-
    Monoid's (lax monoidal functor) laws
    pure id <*> v = v  Identity
    pure f <*> pure x = pure (f x) Homomorphism
    u <*> pure y = pure ($ y) <*> u Interchange
    pure (.) <*> u <*> v <*> w = u <*> (v <*> w) Composition

    Identity
    pure id <*> v = v
    { pure def x2 }
    LDL [(mempty, (0, id))] <*> v = v
    { <*> def x2 }
    forall (w, (d, v')) in v => LDL [(mempty <> w, (0 + d, id v'))] = v
    { mempty <> z = z, nat id, 0 + d = d }
    forall (w, (d, v')) in v => LDL [(w, (d, v')] = v
    { LDL [(w, (d, v'))] = v }
    v = v

    Homomorphism
    pure f <*> pure x = pure (f x)
    { pure def x2 }
    LDL [(mempty, (0, f))] <*> LDL [(mempty, (0, x))] = pure (f x)
    { <*> def, pure def }
    LDL [(mempty, (0, f x))] = LDL [(mempty, (0, f x))]

    Interchange
    u <*> pure y = pure ($ y) <*> u
    { pure def x2, ($ y) = \f -> f y }
    u <*> LDL [(mempty, (0, y))] = LDL [(mempty, (0, (\f -> f y)))] <*> u
    { <*> def x2, func ap, mempty <> w = w, d + 0 = d  }
    forall (w, (d, u')) in u => LDL [(w, (d, u' y))] = LDL [(w, (d, u' y)))]

    Composition
    pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
    { pure def }
    LDL [(mempty, (0, (.)))] <*> u <*> v <*> w = u <*> (v <*> w)
    { <*> def , mempty <> w = w, d + 0 = d  }
    forall (w', (d', u')) in u => LDL [(w', (d', (u' . )))] <*> v <*> w = u <*> (v <*> w)
    { <*> def, uap = LDL [(mempty, (0, (.)))] <*> u }
    forall (w', (d', (u' . ))) in uap, forall (w'', (d'', v')) in v =>  LDL [(w' <> w'', (d'+d'', (u' . v')))] <*> w = u <*> (v <*> w)
    { <*> def, uvap = LDL [(mempty, (0, (.)))] <*> u <*> v  }
    forall (w' <> w'', (d'+d'', (u' . v'))) in uvap, forall (w''', (d''', w')) in w => LDL [(w' <> w'' <> w''', (d'+d''+d''', (u' . v') w'))]
    { (f . g) x = f (g x) }
    { left  = LDL [(w' <> w'' <> w''', (d'+d''+d''', u' (v' w')))] }
    { <*> def }
    forall (w'', (d'', v')) in v, forall (w''', (d''', w')) in w =>  u <*> LDL [(w'' <> w''', (d''+d''', v' w'))]
    { <*> def, vap = v <*> w }
    forall (w', (d', u')) in u, forall (w'' <> w''', (d''+d''', v' w')) in vap => LDL [(w' <> w'' <> w''', (d'+d''+d''', u' (v' w')))]
    { right = LDL [(w' <> w'' <> w''', (d'+d''+d''', u' (v' w')))] = left }
-}

instance Monoid w => Monad (ListDurLog w) where
   return = pure
   l >>= k = LDL $ remLDL l >>= (\(w, (Duration (s, x))) ->
        fmap (\(w', (Duration (s', z))) -> (w <> w', Duration (s + s', z))) . remLDL . k $ x)


allValidPlaysD :: State -> ListDurLog String State
allValidPlaysD s =
    let fLSide  = s . Right $ ()
        valid   = foldr (\p a -> if fLSide == s (Left p) then p:a else a) [] [P1, P2, P5, P10]
        pairs l = [(x,y) | (x:ys) <- tails l, y <- x:ys]
        backOrForth s0 p = if s0 p then (<> "crossed back the bridge >") else (<> "crossed the bridge >")
     in LDL $ do
         (p', p'') <- pairs valid
         if p' == p'' then return ( backOrForth s (Left p') (show p' <> " ")
                                  , Duration (getTimeAdv p', mChangeState [Left p', Right ()] s)
                                  )
                      else return ( backOrForth s (Left p') (show p' <> " and " <> show p'' <> " both ")
                                  , Duration ( max (getTimeAdv p') (getTimeAdv p'')
                                             , mChangeState [Left p', Left p'', Right ()] s
                                             )
                                  )

execD :: Int -> State -> ListDurLog String State
execD 0 _ = LDL []
execD 1 s = allValidPlaysD s
execD n s = allValidPlaysD s >>= execD (n-1)

getPathN :: Int -> ListDurLog w State -> ListDurLog w [Bool]
getPathN n = filterAllCrossed . applyStateChange . filterByDuration n where
    filterByDuration x = LDL . filter ((==x) . getDuration . snd) . remLDL
    applyStateChange = fmap (<$> adv)
    filterAllCrossed = LDL . filter (all (==True) . getValue . snd) . remLDL

printPathByTime :: Int -> ListDurLog String State -> IO String
printPathByTime = cond null noPath printEachAction ... getPaths where
        getPaths = remLDL ... getPathN
        noPath _ = putStrLn err >> return err
        printEachAction p = (mapM_ putStrLn . wordsWhen (=='>') . fst . head) p >> return []
        err = "No path available"

--------------------------------------------------------------------------------
-- Aux stuff

wordsWhen :: (Char -> Bool) -> String -> [String]
wordsWhen p s =
    case dropWhile p s of
        "" -> []
        s' -> w : wordsWhen p s'' where
                (w, s'') = break p s'

cond :: (b -> Bool) -> (b -> c) -> (b -> c) -> b -> c
cond p f g = either f g . grd p where
  grd :: (a -> Bool) -> a -> Either a a
  grd pr x = if pr x then Left x else Right x

-- black bird
(...) = (.) . (.)

adv :: [Objects]
adv = [Left P1, Left P2, Left P5, Left P10, Right ()]

run :: [Int] -> [Int] -> IO ()
run times moves = do
    allQueries
    putStrLn ""
    let sucess t0 m0 = putStrLn $ " (All in " <> show t0 <> " minutes and " <> show m0 <> " step(s))"
    let err t0 m0 = putStrLn $ " (For " <> show t0 <> " minutes and " <> show m0 <> " step(s))"
    let s = zipWith (\t m -> printPathByTime t (execD m gInit) >>= (\s -> if null s then sucess t m else err t m))
    sequence_ . intersperse (putStrLn "") $ s times moves



interface :: IO ()
interface = loop gInit 0

loop :: State -> Int -> IO ()
loop s time = do
    putStr "\ESC[2J"
    putStrLn $ "Time elapsed: " <> show time <> " minute(s)"
    putStrLn "\n"
    ppState s
    putStrLn ""
    let plays = remLDL . allValidPlaysD $ s
    putStrLn "Possible actions: "
    mapM_ (\(t, n) -> putStrLn (t <> " " <> show n)) . fst . foldl' (\(acc, n) (w, _) -> ((w, n):acc, n+1)) ([], 0) $ plays
    putStr "> "
    choice <- read <$> getLine
    if choice `elem` [0..(length plays)-1]
       then do
           let (w, (Duration (d, s'))) = plays !! choice
           putStrLn w
           loop s' (d+time)
       else loop s time


ppState :: State -> IO ()
ppState s = do
    let (left, right) = foldr (\(p, b) (l, r) -> if b then (l, p:r) else (p:l, r)) ([], []) . fmap (\p -> (p, s p)) $ adv
    let ppSide = cond null (const (putStr "{}")) (mapM_ (putStr . either (\p -> show p <> " ") (const "Flashlight ")))
    ppSide left
    putStr " #----------# "
    ppSide right
    putStrLn ""
