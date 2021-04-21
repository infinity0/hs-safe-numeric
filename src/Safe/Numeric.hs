{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeSynonymInstances  #-}

{- | Safe arithmetic operations.

We take a fairly conservative approach here - this module is an extension not
a replacement for "Prelude". Our suffix naming conventions are as follows:

- @\@@ or @W@ -- wrap - same as "Prelude", but confirms explicitly to the
  reader that you thought about the issue
- @%@ or @E@ -- explicit error (@'Either' 'ArithException'@)
- @:@ or @S@ -- saturate at 'minBound' or 'maxBound'
- @!@ or @X@ -- runtime exception. This is suitable only for trusted inputs,
  since otherwise you allow the attacker to crash your code arbitrarily.

Currently we provide replacements for:

- conversion functions 'fromIntegral' and 'fromInteger'; instead use

    - 'ex' for cost-free conversions to a bigger or same-sized type, or
    - 'ctW', 'ctE', 'ctS', or 'ctX' for checked conversions to a smaller type

- arithmetic functions '+', '-', '*', '^'; instead use

    - '+@', '+%', '+:', '+!', etc

- division functions 'div', 'mod', 'divMod', 'quot', 'rem', 'quotRem'; instead use

    - 'divE', 'divX', etc

When using this module, you might also like to ban the unsafe functions from
your codebase, e.g. via hlint:

@
- functions:
  - {name: [fromIntegral, fromInteger, +, \'-\', \'*\', ^], within: [], message: "Use safe versions from Safe.Numeric"}
  - {name: [div, mod, divMod, quot, rem, quotRem], within: [], message: "Use safe versions from Safe.Numeric"}
@

-}
module Safe.Numeric
  ( Word29_
  , Int29_
  -- * Conversions
  , NumExpand(..)
  , NumConvert(..)
  -- * Arithmetic
  , (+@)
  , (+%)
  , (+:)
  , (+!)
  , (-@)
  , (-%)
  , (-:)
  , (-!)
  , (*@)
  , (*%)
  , (*:)
  , (*!)
  , (^@)
  , (^%)
  , (^:)
  , (^!)
  -- * Division
  , DivResult
  , divE
  , divX
  , modE
  , modX
  , divModE
  , divModX
  , quotE
  , quotX
  , remE
  , remX
  , quotRemE
  , quotRemX
  ) where

-- external
import           Control.Exception (ArithException (..))
import           Data.Int
import           Data.WideWord
import           Data.Word
import           Safe.Partial      (Partial)


class NumExpand b a where
  {- | Safely expand type @b@ into type @a@, with no runtime bounds checking.

  a.k.a. "'fromIntegral' hurts my fingers and my eyes"

  The value is statically guaranteed to remain the same relative to 0 in both
  directions, i.e. not overflow or underflow, without any runtime checks.
  -}
  ex :: b -> a
  default ex :: (Num a, Integral b) => b -> a
  ex = fromIntegral
  {-# INLINE ex #-}

checkE
  :: forall a . (Integral a, Bounded a) => Integer -> Either ArithException a
checkE v | v < toInteger (minBound :: a) = Left Underflow
         | v > toInteger (maxBound :: a) = Left Overflow
         | otherwise                     = Right (fromInteger v)
{-# INLINE checkE #-}

checkS :: forall a . (Integral a, Bounded a) => Integer -> a
checkS v | v < toInteger (minBound :: a) = minBound
         | v > toInteger (maxBound :: a) = maxBound
         | otherwise                     = fromInteger v
{-# INLINE checkS #-}

checkX :: forall a . (Integral a, Bounded a) => Partial => Integer -> a
checkX v | v < toInteger (minBound :: a) = error "Underflow"
         | v > toInteger (maxBound :: a) = error "Overflow"
         | otherwise                     = fromInteger v
{-# INLINE checkX #-}

-- | Convert from a type into a smaller type
class NumConvert b a where

  -- | Wrap around if the input is out-of-bounds.
  ctW :: b -> a
  default ctW :: (Num a, Integral b) => b -> a
  ctW b = fromIntegral b
  {-# INLINE ctW #-}

  -- | Explicit error if the input is out-of-bounds.
  ctE :: b -> Either ArithException a
  default ctE :: (Integral a, Bounded a, Integral b) => b -> Either ArithException a
  ctE = checkE . toInteger
  {-# INLINE ctE #-}

  -- | Output 'minBound' if the input is too small, or 'maxBound' if too large.
  ctS :: b -> a
  default ctS :: (Integral a, Bounded a, Integral b) => b -> a
  ctS = checkS . toInteger
  {-# INLINE ctS #-}

  -- | Runtime (async) exception if the input is out-of-bounds.
  ctX :: Partial => b -> a
  default ctX :: (Integral a, Bounded a, Integral b) => Partial => b -> a
  ctX = checkX . toInteger
  {-# INLINE ctX #-}

{- | Type alias for 'Word' that explicitly states its lower-bound size. -}
type Word29_ = Word

{- | Type alias for 'Int' that explicitly states its lower-bound size. -}
type Int29_ = Int

{-

Fr\To W8    W16   W29_  W32   W64   W128  W256  I8    I16   I29_  I32   I64   I128  I256  Itgr
W8    X     X     X     X     X     X     X           X     X     X     X     X     X     X
W16         X     X     X     X     X     X                 X     X     X     X     X     X
W29_              X                                                                       X
W32                     X     X     X     X                             X     X     X     X
W64                           X     X     X                                   X     X     X
W128                                X     X                                         X     X
W256                                      X                                               X
I8                                              X     X     X     X     X     X     X     X
I16                                                   X     X     X     X     X     X     X
I29_                                                        X                             X
I32                                                               X     X     X     X     X
I64                                                                     X     X     X     X
I128                                                                          X     X     X
I256                                                                                X     X
Itgr                                                                                      X

In the above table, X means NumExpand, empty means NumConvert

Safe-nocheck-expand from W29_ and I29_ to other bounded types are not
guaranteed since there is no specified upper bound on the sizes of the former.

Generally, we cannot have (NumExpand a b) *and* (NumExpand b a) unless b = a.
-}

-- note: wide-word does not yet define Int256, so references to it below are
-- commented out

instance NumExpand Word8 Word8
instance NumExpand Word8 Word16
instance NumExpand Word8 Word29_
instance NumExpand Word8 Word32
instance NumExpand Word8 Word64
instance NumExpand Word8 Word128
instance NumExpand Word8 Word256
instance NumConvert Word8 Int8
instance NumExpand Word8 Int16
instance NumExpand Word8 Int29_
instance NumExpand Word8 Int32
instance NumExpand Word8 Int64
instance NumExpand Word8 Int128
--instance NumExpand Word8 Int256
instance NumExpand Word8 Integer

instance NumConvert Word16 Word8
instance NumExpand Word16 Word16
instance NumExpand Word16 Word29_
instance NumExpand Word16 Word32
instance NumExpand Word16 Word64
instance NumExpand Word16 Word128
instance NumExpand Word16 Word256
instance NumConvert Word16 Int8
instance NumConvert Word16 Int16
instance NumExpand Word16 Int29_
instance NumExpand Word16 Int32
instance NumExpand Word16 Int64
instance NumExpand Word16 Int128
--instance NumExpand Word16 Int256
instance NumExpand Word16 Integer

instance NumConvert Word29_ Word8
instance NumConvert Word29_ Word16
instance NumExpand Word29_ Word29_
instance NumConvert Word29_ Word32
instance NumConvert Word29_ Word64
instance NumConvert Word29_ Word128
instance NumConvert Word29_ Word256
instance NumConvert Word29_ Int8
instance NumConvert Word29_ Int16
instance NumConvert Word29_ Int29_
instance NumConvert Word29_ Int32
instance NumConvert Word29_ Int64
instance NumConvert Word29_ Int128
--instance NumConvert Word29_ Int256
instance NumExpand Word29_ Integer

instance NumConvert Word32 Word8
instance NumConvert Word32 Word16
instance NumConvert Word32 Word29_
instance NumExpand Word32 Word32
instance NumExpand Word32 Word64
instance NumExpand Word32 Word128
instance NumExpand Word32 Word256
instance NumConvert Word32 Int8
instance NumConvert Word32 Int16
instance NumConvert Word32 Int29_
instance NumConvert Word32 Int32
instance NumExpand Word32 Int64
instance NumExpand Word32 Int128
--instance NumExpand Word32 Int256
instance NumExpand Word32 Integer

instance NumConvert Word64 Word8
instance NumConvert Word64 Word16
instance NumConvert Word64 Word29_
instance NumConvert Word64 Word32
instance NumExpand Word64 Word64
instance NumExpand Word64 Word128
instance NumExpand Word64 Word256
instance NumConvert Word64 Int8
instance NumConvert Word64 Int16
instance NumConvert Word64 Int29_
instance NumConvert Word64 Int32
instance NumConvert Word64 Int64
instance NumExpand Word64 Int128
--instance NumExpand Word64 Int256
instance NumExpand Word64 Integer

instance NumConvert Word128 Word8
instance NumConvert Word128 Word16
instance NumConvert Word128 Word29_
instance NumConvert Word128 Word32
instance NumConvert Word128 Word64
instance NumExpand Word128 Word128
instance NumExpand Word128 Word256
instance NumConvert Word128 Int8
instance NumConvert Word128 Int16
instance NumConvert Word128 Int29_
instance NumConvert Word128 Int32
instance NumConvert Word128 Int64
instance NumConvert Word128 Int128
--instance NumExpand Word128 Int256
instance NumExpand Word128 Integer

instance NumConvert Word256 Word8
instance NumConvert Word256 Word16
instance NumConvert Word256 Word29_
instance NumConvert Word256 Word32
instance NumConvert Word256 Word64
instance NumConvert Word256 Word128
instance NumExpand Word256 Word256
instance NumConvert Word256 Int8
instance NumConvert Word256 Int16
instance NumConvert Word256 Int29_
instance NumConvert Word256 Int32
instance NumConvert Word256 Int64
instance NumConvert Word256 Int128
--instance NumConvert Word256 Int256
instance NumExpand Word256 Integer

instance NumConvert Int8 Word8
instance NumConvert Int8 Word16
instance NumConvert Int8 Word29_
instance NumConvert Int8 Word32
instance NumConvert Int8 Word64
instance NumConvert Int8 Word128
instance NumConvert Int8 Word256
instance NumExpand Int8 Int8
instance NumExpand Int8 Int16
instance NumExpand Int8 Int29_
instance NumExpand Int8 Int32
instance NumExpand Int8 Int64
instance NumExpand Int8 Int128
--instance NumExpand Int8 Int256
instance NumExpand Int8 Integer

instance NumConvert Int16 Word8
instance NumConvert Int16 Word16
instance NumConvert Int16 Word29_
instance NumConvert Int16 Word32
instance NumConvert Int16 Word64
instance NumConvert Int16 Word128
instance NumConvert Int16 Word256
instance NumConvert Int16 Int8
instance NumExpand Int16 Int16
instance NumExpand Int16 Int29_
instance NumExpand Int16 Int32
instance NumExpand Int16 Int64
instance NumExpand Int16 Int128
--instance NumExpand Int16 Int256
instance NumExpand Int16 Integer

instance NumConvert Int29_ Word8
instance NumConvert Int29_ Word16
instance NumConvert Int29_ Word29_
instance NumConvert Int29_ Word32
instance NumConvert Int29_ Word64
instance NumConvert Int29_ Word128
instance NumConvert Int29_ Word256
instance NumConvert Int29_ Int8
instance NumConvert Int29_ Int16
instance NumExpand Int29_ Int29_
instance NumConvert Int29_ Int32
instance NumConvert Int29_ Int64
instance NumConvert Int29_ Int128
--instance NumConvert Int29_ Int256
instance NumExpand Int29_ Integer

instance NumConvert Int32 Word8
instance NumConvert Int32 Word16
instance NumConvert Int32 Word29_
instance NumConvert Int32 Word32
instance NumConvert Int32 Word64
instance NumConvert Int32 Word128
instance NumConvert Int32 Word256
instance NumConvert Int32 Int8
instance NumConvert Int32 Int16
instance NumConvert Int32 Int29_
instance NumExpand Int32 Int32
instance NumExpand Int32 Int64
instance NumExpand Int32 Int128
--instance NumExpand Int32 Int256
instance NumExpand Int32 Integer

instance NumConvert Int64 Word8
instance NumConvert Int64 Word16
instance NumConvert Int64 Word29_
instance NumConvert Int64 Word32
instance NumConvert Int64 Word64
instance NumConvert Int64 Word128
instance NumConvert Int64 Word256
instance NumConvert Int64 Int8
instance NumConvert Int64 Int16
instance NumConvert Int64 Int29_
instance NumConvert Int64 Int32
instance NumExpand Int64 Int64
instance NumExpand Int64 Int128
--instance NumExpand Int64 Int256
instance NumExpand Int64 Integer

instance NumConvert Int128 Word8
instance NumConvert Int128 Word16
instance NumConvert Int128 Word29_
instance NumConvert Int128 Word32
instance NumConvert Int128 Word64
instance NumConvert Int128 Word128
instance NumConvert Int128 Word256
instance NumConvert Int128 Int8
instance NumConvert Int128 Int16
instance NumConvert Int128 Int29_
instance NumConvert Int128 Int32
instance NumConvert Int128 Int64
instance NumExpand Int128 Int128
--instance NumExpand Int128 Int256
instance NumExpand Int128 Integer

{-instance NumConvert Int256 Word8
instance NumConvert Int256 Word16
instance NumConvert Int256 Word29_
instance NumConvert Int256 Word32
instance NumConvert Int256 Word64
instance NumConvert Int256 Word128
instance NumConvert Int256 Word256
instance NumConvert Int256 Int8
instance NumConvert Int256 Int16
instance NumConvert Int256 Int29_
instance NumConvert Int256 Int32
instance NumConvert Int256 Int64
instance NumConvert Int256 Int128
instance NumExpand Int256 Int256
instance NumExpand Int256 Integer-}

instance NumConvert Integer Word8
instance NumConvert Integer Word16
instance NumConvert Integer Word29_
instance NumConvert Integer Word32
instance NumConvert Integer Word64
instance NumConvert Integer Word128
instance NumConvert Integer Word256
instance NumConvert Integer Int8
instance NumConvert Integer Int16
instance NumConvert Integer Int29_
instance NumConvert Integer Int32
instance NumConvert Integer Int64
instance NumConvert Integer Int128
--instance NumConvert Integer Int256
instance NumExpand Integer Integer

{- | Add with wrap-around.

Same as 'Prelude.+' but indicates to the reader that you explicitly thought
about this issue and decided that wrap-around is the correct behaviour.
-}
(+@) :: Num a => a -> a -> a
(+@) = (+)
infixl 6 +@
{-# INLINE (+@) #-}

-- | Add with explicit error on overflow or underflow.
(+%) :: (Integral a, Bounded a) => a -> a -> Either ArithException a
(+%) a b = checkE $ toInteger a + toInteger b
infixl 6 +%
{-# INLINE (+%) #-}

-- | Add with output 'maxBound' on overflow or 'minBound' on underflow.
(+:) :: (Integral a, Bounded a) => a -> a -> a
(+:) a b = checkS $ toInteger a + toInteger b
infixl 6 +:
{-# INLINE (+:) #-}

-- | Add with runtime (async) exception on overflow or underflow.
(+!) :: (Integral a, Bounded a) => Partial => a -> a -> a
(+!) a b = checkX $ toInteger a + toInteger b
infixl 6 +!
{-# INLINE (+!) #-}

{- | Subtract with wrap-around.

Same as 'Prelude.-' but indicates to the reader that you explicitly thought
about this issue and decided that wrap-around is the correct behaviour.
-}
(-@) :: Num a => a -> a -> a
(-@) = (-)
infixl 6 -@
{-# INLINE (-@) #-}

-- | Subtract with explicit error on overflow or underflow.
(-%) :: (Integral a, Bounded a) => a -> a -> Either ArithException a
(-%) a b = checkE $ toInteger a - toInteger b
infixl 6 -%
{-# INLINE (-%) #-}

-- | Subtract with output 'maxBound' on overflow or 'minBound' on underflow.
(-:) :: (Integral a, Bounded a) => a -> a -> a
(-:) a b = checkS $ toInteger a - toInteger b
infixl 6 -:
{-# INLINE (-:) #-}

-- | Subtract with runtime (async) exception on overflow or underflow.
(-!) :: (Integral a, Bounded a) => Partial => a -> a -> a
(-!) a b = checkX $ toInteger a - toInteger b
infixl 6 -!
{-# INLINE (-!) #-}

{- | Multiply with wrap-around.

Same as 'Prelude.*' but indicates to the reader that you explicitly thought
about this issue and decided that wrap-around is the correct behaviour.
-}
(*@) :: Num a => a -> a -> a
(*@) = (*)
infixl 7 *@
{-# INLINE (*@) #-}

-- | Multiply with explicit error on overflow or underflow.
(*%) :: (Integral a, Bounded a) => a -> a -> Either ArithException a
(*%) a b = checkE $ toInteger a * toInteger b
infixl 7 *%
{-# INLINE (*%) #-}

-- | Multiply with output 'maxBound' on overflow or 'minBound' on underflow.
(*:) :: (Integral a, Bounded a) => a -> a -> a
(*:) a b = checkS $ toInteger a * toInteger b
infixl 7 *:
{-# INLINE (*:) #-}

-- | Multiply with runtime (async) exception on overflow or underflow.
(*!) :: (Integral a, Bounded a) => Partial => a -> a -> a
(*!) a b = checkX $ toInteger a * toInteger b
infixl 7 *!
{-# INLINE (*!) #-}

{- | Power with wrap-around.

Same as 'Prelude.^' but indicates to the reader that you explicitly thought
about this issue and decided that wrap-around is the correct behaviour.
-}
(^@) :: Integral a => a -> a -> a
(^@) = (^)
infixr 8 ^@
{-# INLINE (^@) #-}

-- | Power with explicit error on overflow or underflow.
(^%) :: (Integral a, Bounded a) => a -> a -> Either ArithException a
(^%) a b = checkE $ toInteger a ^ toInteger b
infixr 8 ^%
{-# INLINE (^%) #-}

-- | Power with output 'maxBound' on overflow or 'minBound' on underflow.
(^:) :: (Integral a, Bounded a) => a -> a -> a
(^:) a b = checkS $ toInteger a ^ toInteger b
infixr 8 ^:
{-# INLINE (^:) #-}

-- | Power with runtime (async) exception on overflow or underflow.
(^!) :: (Integral a, Bounded a) => Partial => a -> a -> a
(^!) a b = checkX $ toInteger a ^ toInteger b
infixr 8 ^!
{-# INLINE (^!) #-}

{- | Type alias for a division-operation result with explicit error.

The @Left@ case means /division by zero/, and its parameter represents the
sign of the nominator operand.
-}
type DivResult a = Either Ordering a

explicitDiv :: (Eq a, Ord a, Num a) => (a -> a -> b) -> a -> a -> DivResult b
explicitDiv op x y = if y == 0 then Left $ compare x 0 else Right $ x `op` y
{-# INLINE explicitDiv #-}

-- | Division (truncated towards -Inf) with explicit error on division-by-zero.
divE :: Integral a => a -> a -> DivResult a
divE = explicitDiv div
{-# INLINE divE #-}

{- | Division (truncated towards -Inf) with runtime (async) exception on division-by-zero.

Same as 'Prelude.div' but indicates to the reader that you explicitly thought
about this issue and decided that runtime exception is the correct behaviour.
-}
divX :: Integral a => a -> a -> a
divX = div
{-# INLINE divX #-}

-- | Modulus (truncated towards -Inf) with explicit error on division-by-zero.
modE :: Integral a => a -> a -> DivResult a
modE = explicitDiv mod
{-# INLINE modE #-}

{- | Modulus (truncated towards -Inf) with runtime (async) exception on division-by-zero.

Same as 'Prelude.mod' but indicates to the reader that you explicitly thought
about this issue and decided that runtime exception is the correct behaviour.
-}
modX :: Integral a => a -> a -> a
modX = mod
{-# INLINE modX #-}

-- | Division-and-modulus (truncated towards -Inf) with explicit error on division-by-zero.
divModE :: Integral a => a -> a -> DivResult (a, a)
divModE = explicitDiv divMod
{-# INLINE divModE #-}

{- | Division-and-modulus (truncated towards -Inf) with runtime (async) exception on division-by-zero.

Same as 'Prelude.divMod' but indicates to the reader that you explicitly thought
about this issue and decided that runtime exception is the correct behaviour.
-}
divModX :: Integral a => a -> a -> (a, a)
divModX = divMod
{-# INLINE divModX #-}

-- | Division (truncated towards 0) with explicit error on division-by-zero.
quotE :: Integral a => a -> a -> DivResult a
quotE = explicitDiv quot
{-# INLINE quotE #-}

{- | Division (truncated towards 0) with runtime (async) exception on division-by-zero.

Same as 'Prelude.quot' but indicates to the reader that you explicitly thought
about this issue and decided that runtime exception is the correct behaviour.
-}
quotX :: Integral a => a -> a -> a
quotX = quot
{-# INLINE quotX #-}

-- | Modulus (truncated towards 0) with explicit error on division-by-zero.
remE :: Integral a => a -> a -> DivResult a
remE = explicitDiv rem
{-# INLINE remE #-}

{- | Modulus (truncated towards 0) with runtime (async) exception on division-by-zero.

Same as 'Prelude.rem' but indicates to the reader that you explicitly thought
about this issue and decided that runtime exception is the correct behaviour.
-}
remX :: Integral a => a -> a -> a
remX = rem
{-# INLINE remX #-}

-- | Division-and-modulus (truncated towards 0) with explicit error on division-by-zero.
quotRemE :: Integral a => a -> a -> DivResult (a, a)
quotRemE = explicitDiv quotRem
{-# INLINE quotRemE #-}

{- | Division-and-modulus (truncated towards 0) with runtime (async) exception on division-by-zero.

Same as 'Prelude.quotRem' but indicates to the reader that you explicitly thought
about this issue and decided that runtime exception is the correct behaviour.
-}
quotRemX :: Integral a => a -> a -> (a, a)
quotRemX = quotRem
{-# INLINE quotRemX #-}
