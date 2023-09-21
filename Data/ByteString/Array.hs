{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}

-- 
-- Copyright (c) 2008-2009, Tom Harper
--           (c) 2009, 2010, 2011 Bryan O'Sullivan
-- All rights reserved.

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions
-- are met:

--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.

--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.

-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
-- A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
-- OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
-- SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
-- LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
-- DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
-- THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
-- OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

module Data.ByteString.Array
    (
    -- * Types
      Array(..),
      MArray(..),
      new,
      newFilled,
      unsafeWrite,
      unsafeFreeze,
      run,
      unsafeIndex,
      toList,
      unsafeIndexM,

    ) where

import GHC.ST (ST(..), runST)
import GHC.Exts hiding (toList)
import GHC.Word (Word8 (W8#))

-- | Immutable array type.
data Array = ByteArray ByteArray#

-- | Mutable array type
data MArray s = MutableByteArray (MutableByteArray# s)

-- | Create an uninitialized mutable array.
new :: forall s. Int -> ST s (MArray s)
new (I# len#)
   = ST $ \s1# ->
      case newByteArray# len# s1# of
        (# s2#, marr# #) -> (# s2#, MutableByteArray marr# #)
{-# INLINE new #-}

-- | Create a mutable array filled with some value.
newFilled :: Int -> Int -> ST s (MArray s)
newFilled (I# len#) (I# c#) = ST $ \s1# ->
  case newByteArray# len# s1# of
    (# s2#, marr# #) -> case setByteArray# marr# 0# len# c# s2# of
      s3# -> (# s3#, MutableByteArray marr# #)
{-# INLINE newFilled #-}

-- | Unchecked write of a mutable array.
unsafeWrite :: MArray s -> Int -> Word8 -> ST s ()
unsafeWrite ma@(MutableByteArray marr) i@(I# i#) (W8# e#) =
  ST $ \s1# -> case writeWord8Array# marr i# e# s1# of
    s2# -> (# s2#, () #)
{-# INLINE unsafeWrite #-}

-- | Freeze a mutable array. Do not mutate the 'MArray' afterwards!
unsafeFreeze :: MArray s -> ST s Array
unsafeFreeze (MutableByteArray marr) = ST $ \s1# ->
    case unsafeFreezeByteArray# marr s1# of
        (# s2#, ba# #) -> (# s2#, ByteArray ba# #)
{-# INLINE unsafeFreeze #-}

-- | Run an action in the ST monad and return an immutable array of
-- its result.
run :: (forall s. ST s (MArray s)) -> Array
run k = runST (k >>= unsafeFreeze)

-- | Unchecked read of an immutable array.  May return garbage or
-- crash on an out-of-bounds access.
unsafeIndex :: Array -> Int -> Word8
unsafeIndex (ByteArray arr) i@(I# i#) =
  case indexWord8Array# arr i# of r# -> W8# r#
{-# INLINE unsafeIndex #-}

-- | Unchecked read of an mutable array.  May return garbage or
-- crash on an out-of-bounds access.
unsafeIndexM :: MArray s -> Int -> ST s Word8
unsafeIndexM (MutableByteArray marr) i@(I# i#) =
  ST $ \s1# -> case readWord8Array# marr i# s1# of 
    (# s2#, e# #) -> (# s2#, W8# e# #)
{-# INLINE unsafeIndexM #-}

-- | Convert an immutable array to a list.
toList :: Array -> Int -> Int -> [Word8]
toList ary off len = loop 0
    where loop i | i < len   = unsafeIndex ary (off+i) : loop (i+1)
                 | otherwise = []
