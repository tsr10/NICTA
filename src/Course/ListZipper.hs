{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Course.ListZipper where

import Course.Core
import Course.List
import Course.Optional
import Course.Functor
import Course.Apply
import Course.Applicative
import Course.Extend
import Course.Comonad
import Course.Traversable
import qualified Prelude as P

-- $setup
-- >>> import Test.QuickCheck
-- >>> import Data.Maybe(maybe)
-- >>> import Course.Core
-- >>> import qualified Prelude as P
-- >>> let optional e _ Empty = e; optional _ f (Full a) = f a
-- >>> instance Arbitrary a => Arbitrary (Optional a) where arbitrary = P.fmap (maybe Empty Full) arbitrary
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap (P.foldr (:.) Nil) arbitrary
-- >>> instance Arbitrary a => Arbitrary (ListZipper a) where arbitrary = do l <- arbitrary; x <- arbitrary; r <- arbitrary; P.return (ListZipper l x r)

-- A `ListZipper` is a focussed position, with a list of values to the left and to the right.
--
-- For example, taking the list [0,1,2,3,4,5,6], the moving focus to the third position, the zipper looks like:
-- ListZipper [2,1,0] 3 [4,5,6]
--
-- Supposing then we move left on this zipper:
-- ListZipper [1,0] 2 [3,4,5,6]
--
-- then suppose we add 17 to the focus of this zipper:
-- ListZipper [1,0] 19 [3,4,5,6]
data ListZipper a =
  ListZipper (List a) a (List a)
  deriving Eq

lefts ::
  ListZipper a
  -> List a
lefts (ListZipper l _ _) =
  l

rights ::
  ListZipper a
  -> List a
rights (ListZipper _ _ r) =
  r

-- A `MaybeListZipper` is a data structure that allows us to "fail" zipper operations.
-- e.g. Moving left when there are no values to the left.
--
-- We then overload operations polymorphically to operate on both `ListZipper` and `MaybeListZipper`
-- using the `ListZipper'` type-class below.
data MaybeListZipper a =
  IsZ (ListZipper a)
  | IsNotZ
  deriving Eq

-- | Implement the `Functor` instance for `ListZipper`.
--
-- >>> (+1) <$> (zipper [3,2,1] 4 [5,6,7])
-- [4,3,2] >5< [6,7,8]
instance Functor ListZipper where
  (<$>) f (ListZipper a b c) = (ListZipper (f <$> a) (f b) (f <$> c))

-- | Implement the `Functor` instance for `MaybeListZipper`.
--
-- >>> (+1) <$> (IsZ (zipper [3,2,1] 4 [5,6,7]))
-- [4,3,2] >5< [6,7,8]
instance Functor MaybeListZipper where
  (<$>) f IsNotZ = IsNotZ
  (<$>) f (IsZ a) = IsZ (f <$> a)

-- | Create a `MaybeListZipper` positioning the focus at the head.
--
-- ->>> fromList (1 :. 2 :. 3 :. Nil)
-- [] >1< [2,3]
--
-- >>> fromList Nil
-- ><
--
-- prop> xs == toListZ (fromList xs)
fromList ::
  List a
  -> MaybeListZipper a
fromList Nil = IsNotZ
fromList (x :. xs) = IsZ (ListZipper Nil x xs)

-- | Retrieve the `ListZipper` from the `MaybeListZipper` if there is one.
--
-- prop> isEmpty xs == (toOptional (fromList xs) == Empty)
--
-- prop> toOptional (fromOptional z) == z
toOptional ::
  MaybeListZipper a
  -> Optional (ListZipper a)
toOptional (IsZ a) = Full a
toOptional (IsNotZ) = Empty

zipper ::
  [a]
  -> a
  -> [a]
  -> ListZipper a
zipper l x r =
  ListZipper (listh l) x (listh r)

fromOptional ::
  Optional (ListZipper a)
  -> MaybeListZipper a
fromOptional Empty =
  IsNotZ
fromOptional (Full z) =
  IsZ z

asZipper ::
  (ListZipper a -> ListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
asZipper f =
  asMaybeZipper (IsZ . f)

(>$>)::
  (ListZipper a -> ListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
(>$>) =
  asZipper

asMaybeZipper ::
  (ListZipper a -> MaybeListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
asMaybeZipper _ IsNotZ =
  IsNotZ
asMaybeZipper f (IsZ z) =
  f z

(-<<) ::
  (ListZipper a -> MaybeListZipper a)
  -> MaybeListZipper a
  -> MaybeListZipper a
(-<<) =
  asMaybeZipper

-- | Convert the given zipper back to a list.
--
-- >>> toList <$> toOptional (fromList Nil)
-- Empty
--
-- >>> toList (ListZipper Nil 1 (2:.3:.4:.Nil))
-- [1,2,3,4]
--
-- >>> toList (ListZipper (3:.2:.1:.Nil) 4 (5:.6:.7:.Nil))
-- [1,2,3,4,5,6,7]
toList ::
  ListZipper a
  -> List a
toList (ListZipper a b c) = reverse(a) ++ (listh [b]) ++ c

-- | Convert the given (maybe) zipper back to a list.
toListZ ::
  MaybeListZipper a
  -> List a
toListZ IsNotZ =
  Nil
toListZ (IsZ z) =
  toList z

-- | Update the focus of the zipper with the given function on the current focus.
--
-- >>> withFocus (+1) (zipper [] 0 [1])
-- [] >1< [1]
--
-- >>> withFocus (+1) (zipper [1,0] 2 [3,4])
-- [1,0] >3< [3,4]
withFocus ::
  (a -> a)
  -> ListZipper a
  -> ListZipper a
withFocus f (ListZipper a b c) = ListZipper a (f b) c

-- | Set the focus of the zipper to the given value.
-- /Tip:/ Use `withFocus`.
--
-- >>> setFocus 1 (zipper [] 0 [1])
-- [] >1< [1]
--
-- >>> setFocus 1 (zipper [1,0] 2 [3,4])
-- [1,0] >1< [3,4]
setFocus ::
  a
  -> ListZipper a
  -> ListZipper a
setFocus x (ListZipper a _ c) = ListZipper a x c

-- A flipped infix alias for `setFocus`. This allows:
--
-- z .= "abc" -- sets the focus on the zipper z to the value "abc".
(.=) ::
  ListZipper a
  -> a
  -> ListZipper a
(.=) =
  flip setFocus

-- | Returns whether there are values to the left of focus.
--
-- >>> hasLeft (zipper [1,0] 2 [3,4])
-- True
--
-- >>> hasLeft (zipper [] 0 [1,2])
-- False
hasLeft ::
  ListZipper a
  -> Bool
hasLeft (ListZipper Nil _ _) = False
hasLeft (ListZipper _ _ _) = True

-- | Returns whether there are values to the right of focus.
--
-- >>> hasRight (zipper [1,0] 2 [3,4])
-- True
--
-- >>> hasRight (zipper [1,0] 2 [])
-- False
hasRight ::
  ListZipper a
  -> Bool
hasRight (ListZipper _ _ Nil) = False
hasRight (ListZipper _ _ _) = True

-- | Seek to the left for a location matching a predicate, starting from the
-- current one.
--
-- prop> findLeft (const True) -<< fromList xs == fromList xs
--
-- prop> findLeft (const False) (zipper l x r) == IsNotZ
--
-- >>> findLeft (== 1) (zipper [2, 1] 3 [4, 5])
-- [] >1< [2,3,4,5]
findLeft ::
  (a -> Bool)
  -> ListZipper a
  -> MaybeListZipper a
findLeft f (ListZipper Nil b c) = if (f b) then (IsZ (ListZipper Nil b c)) else IsNotZ
findLeft f (ListZipper (x :. xs) b c) = if (f b) then (IsZ (ListZipper (x :. xs) b c)) else (findLeft f (ListZipper xs x (b :. c)))

-- | Seek to the right for a location matching a predicate, starting from the
-- current one.
--
-- prop> findRight (const True) -<< fromList xs == fromList xs
--
-- prop> findRight (const False) (zipper l x r) == IsNotZ
--
-- >>> findRight (== 5) (zipper [2, 1] 3 [4, 5])
-- [4,3,2,1] >5< []
findRight ::
  (a -> Bool)
  -> ListZipper a
  -> MaybeListZipper a
findRight f (ListZipper a b Nil) = if (f b) then (IsZ (ListZipper a b Nil)) else IsNotZ
findRight f (ListZipper a b (x :. xs)) = if (f b) then (IsZ (ListZipper a b (x :. xs))) else (findRight f (ListZipper (b :. a) x xs))


-- | Move the zipper left, or if there are no elements to the left, go to the far right.
--
-- >>> moveLeftLoop (zipper [3,2,1] 4 [5,6,7])
-- [2,1] >3< [4,5,6,7]
--
-- >>> moveLeftLoop (zipper [] 1 [2,3,4])
-- [3,2,1] >4< []
moveLeftLoop ::
  ListZipper a
  -> ListZipper a
moveLeftLoop (ListZipper Nil b c) = let (y :. ys) = reverse(b :. c) in ListZipper ys y Nil
moveLeftLoop (ListZipper (x :. xs) b c) = ListZipper xs x (b :. c)

-- | Move the zipper right, or if there are no elements to the right, go to the far left.
--
-- >>> moveRightLoop (zipper [3,2,1] 4 [5,6,7])
-- [4,3,2,1] >5< [6,7]
--
-- >>> moveRightLoop (zipper [3,2,1] 4 [])
-- [] >1< [2,3,4]
moveRightLoop ::
  ListZipper a
  -> ListZipper a
moveRightLoop (ListZipper a b Nil) = let (y :. ys) = reverse(b :. a) in ListZipper Nil y ys
moveRightLoop (ListZipper a b (x :. xs)) = ListZipper (b :. a) x xs

-- | Move the zipper one position to the left.
--
-- >>> moveLeft (zipper [3,2,1] 4 [5,6,7])
-- [2,1] >3< [4,5,6,7]
--
-- >>> moveLeft (zipper [] 1 [2,3,4])
-- ><
moveLeft ::
  ListZipper a
  -> MaybeListZipper a
moveLeft (ListZipper Nil b c) = IsNotZ
moveLeft (ListZipper (x :. xs) b c) = IsZ $ ListZipper xs x (b :. c)

-- | Move the zipper one position to the right.
--
-- >>> moveRight (zipper [3,2,1] 4 [5,6,7])
-- [4,3,2,1] >5< [6,7]
--
-- >>> moveRight (zipper [3,2,1] 4 [])
-- ><
moveRight ::
  ListZipper a
  -> MaybeListZipper a
moveRight (ListZipper a b Nil) = IsNotZ
moveRight (ListZipper a b (x :. xs)) = IsZ $ ListZipper (b :. a) x xs

-- | Swap the current focus with the value to the left of focus.
--
-- >>> swapLeft (zipper [3,2,1] 4 [5,6,7])
-- [4,2,1] >3< [5,6,7]
--
-- >>> swapLeft (zipper [] 1 [2,3,4])
-- ><
swapLeft ::
  ListZipper a
  -> MaybeListZipper a
swapLeft (ListZipper Nil b c) = IsNotZ
swapLeft (ListZipper (x :. xs) b c) = IsZ $ ListZipper (b :. xs) x c

-- | Swap the current focus with the value to the right of focus.
--
-- >>> swapRight (zipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >5< [4,6,7]
--
-- >>> swapRight (zipper [3,2,1] 4 [])
-- ><
swapRight ::
  ListZipper a
  -> MaybeListZipper a
swapRight (ListZipper a b Nil) = IsNotZ
swapRight (ListZipper a b (x :. xs)) = IsZ $ ListZipper a x (b :. xs)

-- | Drop all values to the left of the focus.
--
-- >>> dropLefts (zipper [3,2,1] 4 [5,6,7])
-- [] >4< [5,6,7]
--
-- >>> dropLefts (zipper [] 1 [2,3,4])
-- [] >1< [2,3,4]
--
-- prop> dropLefts (zipper l x r) == zipper [] x r
dropLefts ::
  ListZipper a
  -> ListZipper a
dropLefts (ListZipper _ b c) = ListZipper Nil b c

-- | Drop all values to the right of the focus.
--
-- >>> dropRights (zipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >4< []
--
-- >>> dropRights (zipper [3,2,1] 4 [])
-- [3,2,1] >4< []
--
-- prop> dropRights (zipper l x r) == zipper l x []
dropRights ::
  ListZipper a
  -> ListZipper a
dropRights (ListZipper a b _) = ListZipper a b Nil

-- Move the focus left the given number of positions. If the value is negative, move right instead.
moveLeftN ::
  Int
  -> ListZipper a
  -> MaybeListZipper a
moveLeftN n a | (n == 0) = IsZ a
moveLeftN n a | (n < 0) = moveRightN (-n) a
moveLeftN n (ListZipper Nil b c) = IsNotZ
moveLeftN n (ListZipper (x :. xs) b c) = moveLeftN (n - 1) (ListZipper xs x (b :. c))

-- Move the focus right the given number of positions. If the value is negative, move left instead.
moveRightN ::
  Int
  -> ListZipper a
  -> MaybeListZipper a
moveRightN n a | (n == 0) = IsZ a
moveRightN n a | (n < 0) = moveLeftN (-n) a
moveRightN n (ListZipper a b Nil) = IsNotZ
moveRightN n (ListZipper a b (x :. xs)) = moveRightN (n - 1) (ListZipper (b :. a) x xs)

-- | Move the focus left the given number of positions. If the value is negative, move right instead.
-- If the focus cannot be moved, the given number of times, return the value by which it can be moved instead.
--
-- >>> moveLeftN' 4 (zipper [3,2,1] 4 [5,6,7])
-- Left 3
--
-- >>> moveLeftN' 1 (zipper [3,2,1] 4 [5,6,7])
-- Right [2,1] >3< [4,5,6,7]
--
-- >>> moveLeftN' 0 (zipper [3,2,1] 4 [5,6,7])
-- Right [3,2,1] >4< [5,6,7]
--
-- >>> moveLeftN' (-2) (zipper [3,2,1] 4 [5,6,7])
-- Right [5,4,3,2,1] >6< [7]
--
-- >>> moveLeftN' (-4) (zipper [3,2,1] 4 [5,6,7])
-- Left 3
--
-- >>> moveLeftN' 4 (zipper [3,2,1] 4 [5,6,7,8,9])
-- Left 3
--
-- >>> moveLeftN' (-4) (zipper [5,4,3,2,1] 6 [7,8,9])
-- Left 3
moveLeftN' ::
  Int
  -> ListZipper a
  -> Either Int (ListZipper a)
moveLeftN' n l@(ListZipper a b c)
  | (n < 1) = moveRightN' (-n) l
  | (length a < n) = Left (length a)
  | otherwise = let (IsZ x) = moveLeftN n l in Right x


-- | Move the focus right the given number of positions. If the value is negative, move left instead.
-- If the focus cannot be moved, the given number of times, return the value by which it can be moved instead.
--
-- >>> moveRightN' 4 (zipper [3,2,1] 4 [5,6,7])
-- Left 3
--
-- >>> moveRightN' 1 (zipper [3,2,1] 4 [5,6,7])
-- Right [4,3,2,1] >5< [6,7]
--
-- >>> moveRightN' 0 (zipper [3,2,1] 4 [5,6,7])
-- Right [3,2,1] >4< [5,6,7]
--
-- >>> moveRightN' (-2) (zipper [3,2,1] 4 [5,6,7])
-- Right [1] >2< [3,4,5,6,7]
--
-- >>> moveRightN' (-4) (zipper [3,2,1] 4 [5,6,7])
-- Left 3
moveRightN' ::
  Int
  -> ListZipper a
  -> Either Int (ListZipper a)
moveRightN' n l@(ListZipper a b c)
  | (n < 1) = moveLeftN' (-n) l
  | (length c < n) = Left (length c)
  | otherwise = let (IsZ x) = moveRightN n l in Right x


-- | Move the focus to the given absolute position in the zipper. Traverse the zipper only to the extent required.
--
-- >>> nth 1 (zipper [3,2,1] 4 [5,6,7])
-- [1] >2< [3,4,5,6,7]
--
-- >>> nth 5 (zipper [3,2,1] 4 [5,6,7])
-- [5,4,3,2,1] >6< [7]
--
-- >>> nth 8 (zipper [3,2,1] 4 [5,6,7])
-- ><
nth ::
  Int
  -> ListZipper a
  -> MaybeListZipper a
nth n l@(ListZipper a b c)
  | (n < 0) = IsNotZ
  | (n < length a) = moveLeftN ((length a) - n) l
  | (n == length a) = IsZ l
  | (n > length a) = moveRightN (n - (length a)) l

-- | Return the absolute position of the current focus in the zipper.
--
-- >>> index (zipper [3,2,1] 4 [5,6,7])
-- 3
--
-- prop> optional True (\z' -> index z' == i) (toOptional (nth i z))
index ::
  ListZipper a
  -> Int
index (ListZipper a b c) = length a

-- | Move the focus to the end of the zipper.
--
-- >>> end (zipper [3,2,1] 4 [5,6,7])
-- [6,5,4,3,2,1] >7< []
--
-- prop> toList lz == toList (end lz)
--
-- prop> rights (end lz) == Nil
end ::
  ListZipper a
  -> ListZipper a
end l@(ListZipper a b c) = let IsZ x = nth (length a + length c) l in x


size :: 
  ListZipper a
  -> Int
size (ListZipper a b c) = length a + length c
-- | Move the focus to the start of the zipper.
--
-- >>> start (zipper [3,2,1] 4 [5,6,7])
-- [] >1< [2,3,4,5,6,7]
--
-- prop> toList lz == toList (start lz)
--
-- prop> lefts (start lz) == Nil
start ::
  ListZipper a
  -> ListZipper a
start l = let IsZ x = nth 0 l in x

-- | Delete the current focus and pull the left values to take the empty position.
--
-- >>> deletePullLeft (zipper [3,2,1] 4 [5,6,7])
-- [2,1] >3< [5,6,7]
--
-- >>> deletePullLeft (zipper [] 1 [2,3,4])
-- ><
deletePullLeft ::
  ListZipper a
  -> MaybeListZipper a
deletePullLeft (ListZipper Nil b c) = IsNotZ
deletePullLeft (ListZipper (x :. xs) b c) = IsZ (ListZipper xs x c)

-- | Delete the current focus and pull the right values to take the empty position.
--
-- >>> deletePullRight (zipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >5< [6,7]
--
-- >>> deletePullRight (zipper [3,2,1] 4 [])
-- ><
deletePullRight ::
  ListZipper a
  -> MaybeListZipper a
deletePullRight (ListZipper a b Nil) = IsNotZ
deletePullRight (ListZipper a b (x :. xs)) = IsZ (ListZipper a x xs)

-- | Insert at the current focus and push the left values to make way for the new position.
--
-- >>> insertPushLeft 15 (zipper [3,2,1] 4 [5,6,7])
-- [4,3,2,1] >15< [5,6,7]
--
-- >>> insertPushLeft 15 (zipper [] 1 [2,3,4])
-- [1] >15< [2,3,4]
--
-- prop> optional False (==z) (toOptional (deletePullLeft (insertPushLeft i z)))
insertPushLeft ::
  a
  -> ListZipper a
  -> ListZipper a
insertPushLeft x (ListZipper a b c) = ListZipper (b :. a) x c

-- | Insert at the current focus and push the right values to make way for the new position.
--
-- >>> insertPushRight 15 (zipper [3,2,1] 4 [5,6,7])
-- [3,2,1] >15< [4,5,6,7]
--
-- >>> insertPushRight 15 (zipper [3,2,1] 4 [])
-- [3,2,1] >15< [4]
--
-- prop> optional False (==z) (toOptional (deletePullRight (insertPushRight i z)))
insertPushRight ::
  a
  -> ListZipper a
  -> ListZipper a
insertPushRight x (ListZipper a b c) = ListZipper a x (b :. c)

-- | Implement the `Apply` instance for `ListZipper`.
-- This implementation zips functions with values by function application.
--
-- >>> zipper [(+2), (+10)] (*2) [(*3), (4*), (5+)] <*> zipper [3,2,1] 4 [5,6,7]
-- [5,12] >8< [15,24,12]
instance Apply ListZipper where
  (<*>) (ListZipper a b c) (ListZipper d e f) = ListZipper (zipWith ($) a d) (b e) (zipWith ($) c f)

-- | Implement the `Apply` instance for `MaybeListZipper`.
--
-- /Tip:/ Use `<*>` for `ListZipper`.
--
-- >>> IsZ (zipper [(+2), (+10)] (*2) [(*3), (4*), (5+)]) <*> IsZ (zipper [3,2,1] 4 [5,6,7])
-- [5,12] >8< [15,24,12]
--
-- >>> IsNotZ <*> IsZ (zipper [3,2,1] 4 [5,6,7])
-- ><
--
-- >>> IsZ (zipper [(+2), (+10)] (*2) [(*3), (4*), (5+)]) <*> IsNotZ
-- ><
--
-- >>> IsNotZ <*> IsNotZ
-- ><
instance Apply MaybeListZipper where
  (<*>) (IsZ a) (IsZ b) = IsZ ((<*>) a b)
  (<*>) _ _ = IsNotZ

-- | Implement the `Applicative` instance for `ListZipper`.
-- This implementation produces an infinite list zipper (to both left and right).
--
-- /Tip:/ Use @List#repeat@.
--
-- prop> all . (==) <*> take n . lefts . pure
--
-- prop> all . (==) <*> take n . rights . pure
instance Applicative ListZipper where
  pure a = ListZipper (repeat a) a (repeat a)

-- | Implement the `Applicative` instance for `MaybeListZipper`.
--
-- /Tip:/ Use @pure@ for `ListZipper`.
--
-- prop> let is (IsZ z) = z in all . (==) <*> take n . lefts . is . pure
--
-- prop> let is (IsZ z) = z in all . (==) <*> take n . rights . is . pure
instance Applicative MaybeListZipper where
  pure a = IsZ (pure a)

-- | Implement the `Extend` instance for `ListZipper`.
-- This implementation "visits" every possible zipper value derivable from a given zipper (i.e. all zippers to the left and right).
--
-- /Tip:/ Use @List#unfoldr@.
--
-- >>> id <<= (zipper [2,1] 3 [4,5])
-- [[1] >2< [3,4,5],[] >1< [2,3,4,5]] >[2,1] >3< [4,5]< [[3,2,1] >4< [5],[4,3,2,1] >5< []]
instance Extend ListZipper where
  (<<=) f l@(ListZipper a b c) = ListZipper (unfoldr (\x -> if x > (length a) then Empty else Full (f (let IsZ y = moveLeftN x l in y), x + 1)) 1) (f l) (unfoldr (\x -> if x > (length c) then Empty else Full (f (let IsZ y = moveRightN x l in y), x + 1)) 1)

-- | Implement the `Extend` instance for `MaybeListZipper`.
-- This instance will use the `Extend` instance for `ListZipper`.
--
--
-- id <<= IsNotZ
-- ><
--
-- >>> id <<= (IsZ (zipper [2,1] 3 [4,5]))
-- [[1] >2< [3,4,5],[] >1< [2,3,4,5]] >[2,1] >3< [4,5]< [[3,2,1] >4< [5],[4,3,2,1] >5< []]
instance Extend MaybeListZipper where
  (<<=) f IsNotZ = IsNotZ
  (<<=) f (IsZ a) = IsZ ((<<=) (f . IsZ) a)

-- | Implement the `Comonad` instance for `ListZipper`.
-- This implementation returns the current focus of the zipper.
--
-- >>> copure (zipper [2,1] 3 [4,5])
-- 3
instance Comonad ListZipper where
  copure (ListZipper a b c) = b

-- | Implement the `Traversable` instance for `ListZipper`.
-- This implementation traverses a zipper while running some `Applicative` effect through the zipper.
-- An effectful zipper is returned.
--
-- >>> traverse id (zipper [Full 1, Full 2, Full 3] (Full 4) [Full 5, Full 6, Full 7])
-- Full [1,2,3] >4< [5,6,7]
--
-- >>> traverse id (zipper [Full 1, Full 2, Full 3] (Full 4) [Empty, Full 6, Full 7])
-- Empty
instance Traversable ListZipper where
  traverse f (ListZipper a b c) = (ListZipper) <$> (traverse f a) <*> (f b) <*> (traverse f c)

-- | Implement the `Traversable` instance for `MaybeListZipper`.
--
-- /Tip:/ Use `traverse` for `ListZipper`.
--
-- >>> traverse id IsNotZ
-- ><
--
-- >>> traverse id (IsZ (zipper [Full 1, Full 2, Full 3] (Full 4) [Full 5, Full 6, Full 7]))
-- Full [1,2,3] >4< [5,6,7]
instance Traversable MaybeListZipper where
  traverse f (IsZ l@(ListZipper a b c)) = IsZ <$> (traverse f l)

-----------------------
-- SUPPORT LIBRARIES --
-----------------------

instance Show a => Show (ListZipper a) where
  show (ListZipper l x r) =
    stringconcat [show l, " >", show x, "< ", show r]

instance Show a => Show (MaybeListZipper a) where
  show (IsZ z) = show z
  show IsNotZ = "><"
