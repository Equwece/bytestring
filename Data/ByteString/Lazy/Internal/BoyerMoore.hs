{-# LANGUAGE BangPatterns, FlexibleContexts #-}
{-# OPTIONS_HADDOCK hide, prune #-}
-- |
-- Module         : Data.ByteString.Lazy.Search.Internal.BoyerMoore
-- Copyright      : Daniel Fischer
--                  Chris Kuklewicz
-- Licence        : BSD3
-- Maintainer     : Daniel Fischer <daniel.is.fischer@googlemail.com>
-- Stability      : Provisional
-- Portability    : non-portable (BangPatterns)
--
-- Fast overlapping Boyer-Moore search of both strict and lazy
-- 'S.ByteString' values. Breaking, splitting and replacing
-- using the Boyer-Moore algorithm.
--
-- Descriptions of the algorithm can be found at
-- <http://www-igm.univ-mlv.fr/~lecroq/string/node14.html#SECTION00140>
-- and
-- <http://en.wikipedia.org/wiki/Boyer-Moore_string_search_algorithm>
--
-- Original authors: Daniel Fischer (daniel.is.fischer at googlemail.com) and
-- Chris Kuklewicz (haskell at list.mightyreason.com).

-- Copyright (c)2010, Daniel Fischer

-- All rights reserved.

-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:

--     * Redistributions of source code must retain the above copyright
--       notice, this list of conditions and the following disclaimer.

--     * Redistributions in binary form must reproduce the above
--       copyright notice, this list of conditions and the following
--       disclaimer in the documentation and/or other materials provided
--       with the distribution.

--     * Neither the name of Daniel Fischer nor the names of other
--       contributors may be used to endorse or promote products derived
--       from this software without specific prior written permission.

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


module Data.ByteString.Lazy.Internal.BoyerMoore (breakSubstringL, genByteStrToSearch, occurs, suffShifts) where


-- import Data.ByteString.Search.Substitution

import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as L
import Data.ByteString.Unsafe ( unsafeIndex, unsafeIndex )

import Data.Array.Base
    ( unsafeAt, UArray, unsafeRead, unsafeWrite, unsafeAt )

import Data.Word ( Word8, Word8 )
import Data.Int (Int64)
import Data.Array.ST
import Data.Array.Unboxed
import Control.Monad (when)

import Data.Bits
import qualified System.Random as SR
import Control.Monad (replicateM)
import Data.Word (Word8)
import Data.ByteString.Lazy (pack, empty)
import qualified Data.ByteString.Lazy as DB
import GHC.Int (Int64)

genByteStrToSearch :: Int -> Int -> IO (DB.ByteString, DB.ByteString) 
genByteStrToSearch patLen strLen = do
  sStr <- pack <$> replicateM strLen (SR.randomRIO (0 :: Word8, 255 :: Word8))
  let patOffsetBound = strLen - patLen
  if patOffsetBound < 0
    then return (empty, empty)
    else do
      randOffset <- SR.randomRIO (0, patOffsetBound)
      let sPat = DB.take (fromIntegral $ strLen - randOffset) . DB.drop (fromIntegral randOffset) $ sStr
      return (sPat, sStr)


------------------------------------------------------------------------------
--                        Boyer-Moore Preprocessing                         --
------------------------------------------------------------------------------

{- Table of last occurrences of bytes in the pattern.

For each byte we record the (negated) position of its last
occurrence in the pattern except at the last position.

Thus, if byte b gives a mismatch at pattern position patPos,
we know that we can shift the window right by at least

patPos - (last occurrence of b in init pat)

or, since we negated the positions,

patPos + (occurs pat)

If the byte doesn't occur in the pattern, we can shift the window
so that the start of the pattern is aligned with the byte after this,
hence the default value of 1.

Complexity: O(patLen + size of alphabet)

-}
{- Precondition: non-empty pattern

This invariant is guaranteed by not exporting occurs,
inside this module, we don't call it for empty patterns.

-}
{-# INLINE occurs #-}
occurs :: S.ByteString -> UArray Int Int
occurs pat = runSTUArray (do
    let !patEnd = S.length pat - 1
        {-# INLINE patAt #-}
        patAt :: Int -> Int
        patAt i = fromIntegral (unsafeIndex pat i)
    ar <- newArray (0, 255) 1
    let loop !i
            | i == patEnd   = return ar
            | otherwise     = do
                unsafeWrite ar (patAt i) (-i)
                loop (i + 1)
    loop 0)

{- Table of suffix-shifts.

When a mismatch occurs at pattern position patPos, assumed to be not the
last position in the pattern, the suffix u of length (patEnd - patPos)
has been successfully matched.
Let c be the byte in the pattern at position patPos.

If the sub-pattern u also occurs in the pattern somewhere *not* preceded
by c, let uPos be the position of the last byte in u for the last of
all such occurrences. Then there can be no match if the window is shifted
less than (patEnd - uPos) places, because either the part of the string
which matched the suffix u is not aligned with an occurrence of u in the
pattern, or it is aligned with an occurrence of u which is preceded by
the same byte c as the originally matched suffix.

If the complete sub-pattern u does not occur again in the pattern, or all
of its occurrences are preceded by the byte c, then we can align the
pattern with the string so that a suffix v of u matches a prefix of the
pattern. If v is chosen maximal, no smaller shift can give a match, so
we can shift by at least (patLen - length v).

If a complete match is encountered, we can shift by at least the same
amount as if the first byte of the pattern was a mismatch, no complete
match is possible between these positions.

For non-periodic patterns, only very short suffixes will usually occur
again in the pattern, so if a longer suffix has been matched before a
mismatch, the window can then be shifted entirely past the partial
match, so that part of the string will not be re-compared.
For periodic patterns, the suffix shifts will be shorter in general,
leading to an O(strLen * patLen) worst-case performance.

To compute the suffix-shifts, we use an array containing the lengths of
the longest common suffixes of the entire pattern and its prefix ending
with position pos.

-}
{- Precondition: non-empty pattern -}
{-# INLINE suffShifts #-}
suffShifts :: S.ByteString -> UArray Int Int
suffShifts pat = runSTUArray (do
    let !patLen = S.length pat
        !patEnd = patLen - 1
        !suff   = suffLengths pat
    ar <- newArray (0,patEnd) patLen
    let preShift !idx !j
            | idx < 0   = return ()
            | suff `unsafeAt` idx == idx + 1 = do
                let !shf = patEnd - idx
                    fillToShf !i
                        | i == shf  = return ()
                        | otherwise = do
                            unsafeWrite ar i shf
                            fillToShf (i + 1)
                fillToShf j
                preShift (idx - 1) shf
            | otherwise = preShift (idx - 1) j
        sufShift !idx
            | idx == patEnd = return ar
            | otherwise     = do
                unsafeWrite ar (patEnd - unsafeAt suff idx) (patEnd - idx)
                sufShift (idx + 1)
    preShift (patEnd - 1) 0
    sufShift 0)

{- Table of suffix-lengths.

The value of this array at place i is the length of the longest common
suffix of the entire pattern and the prefix of the pattern ending at
position i.

Usually, most of the entries will be 0. Only if the byte at position i
is the same as the last byte of the pattern can the value be positive.
In any case the value at index patEnd is patLen (since the pattern is
identical to itself) and 0 <= value at i <= (i + 1).

To keep this part of preprocessing linear in the length of the pattern,
the implementation must be non-obvious (the obvious algorithm for this
is quadratic).

When the index under consideration is inside a previously identified
common suffix, we align that suffix with the end of the pattern and
check whether the suffix ending at the position corresponding to idx
is shorter than the part of the suffix up to idx. If that is the case,
the length of the suffix ending at idx is that of the suffix at the
corresponding position. Otherwise extend the suffix as far as possible.
If the index under consideration is not inside a previously identified
common suffix, compare with the last byte of the pattern. If that gives
a suffix of length > 1, for the next index we're in the previous
situation, otherwise we're back in the same situation for the next
index.

-}
{- Precondition: non-empty pattern -}
{-# INLINE suffLengths #-}
suffLengths :: S.ByteString -> UArray Int Int
suffLengths pat = runSTUArray (do
    let !patLen = S.length pat
        !patEnd = patLen - 1
        !preEnd = patEnd - 1
        {-# INLINE patAt #-}
        patAt i = unsafeIndex pat i
        -- last byte for comparisons
        !pe     = patAt patEnd
        -- find index preceding the longest suffix
        dec !diff !j
            | j < 0 || patAt j /= patAt (j + diff) = j
            | otherwise = dec diff (j - 1)
    ar <- newArray_ (0, patEnd)
    unsafeWrite ar patEnd patLen
    let noSuff !i
            | i < 0     = return ar
            | patAt i == pe = do
                let !diff  = patEnd - i
                    !nextI = i - 1
                    !prevI = dec diff nextI
                if prevI == nextI
                    then unsafeWrite ar i 1 >> noSuff nextI
                    else do unsafeWrite ar i (i - prevI)
                            suffLoop prevI preEnd nextI
            | otherwise = do
                unsafeWrite ar i 0
                noSuff (i - 1)
        suffLoop !pre !end !idx
            | idx < 0   = return ar
            | pre < idx =
              if patAt idx /= pe
                then unsafeWrite ar idx 0 >> suffLoop pre (end - 1) (idx - 1)
                else do
                    prevS <- unsafeRead ar end
                    if pre + prevS < idx
                        then do unsafeWrite ar idx prevS
                                suffLoop pre (end - 1) (idx - 1)
                        else do let !prI = dec (patEnd - idx) pre
                                unsafeWrite ar idx (idx - prI)
                                suffLoop prI preEnd (idx - 1)
            | otherwise = noSuff idx
    noSuff preEnd)


------------------------------------------------------------------------------
--                             Helper Functions                             --
------------------------------------------------------------------------------

{-# INLINE strictify #-}
strictify :: L.ByteString -> S.ByteString
strictify = S.concat . L.toChunks

-- drop k bytes from a list of strict ByteStrings
{-# INLINE ldrop #-}
ldrop :: Int -> [S.ByteString] -> [S.ByteString]
ldrop _ [] = []
ldrop k (!h : t)
  | k < l     = S.drop k h : t
  | otherwise = ldrop (k - l) t
    where
      !l = S.length h

{-# INLINE lsplit #-}
lsplit :: Int -> [S.ByteString] -> ([S.ByteString], [S.ByteString])
lsplit _ [] = ([],[])
lsplit !k (!h : t)
  = case compare k l of
      LT -> ([S.take k h], S.drop k h : t)
      EQ -> ([h], t)
      GT -> let (u, v) = lsplit (k - l) t in (h : u, v)
  where
    !l = S.length h

-- release is used to keep the zipper in lazySearcher from remembering
-- the leading part of the searched string.  The deep parameter is the
-- number of characters that the past needs to hold.  This ensures
-- lazy streaming consumption of the searched string.
{-# INLINE release #-}
release :: Int ->  [S.ByteString] -> [S.ByteString]
release !deep _
    | deep <= 0 = []
release !deep (!x:xs) = let !rest = release (deep-S.length x) xs in x : rest
release _ [] = error "stringsearch.release could not find enough past!"

-- keep is like release, only we mustn't forget the part of the past
-- we don't need anymore for matching but have to keep it for
-- breaking, splitting and replacing.
-- The names would be more appropriate the other way round, but that's
-- a historical accident, so what?
{-# INLINE keep #-}
keep :: Int -> [S.ByteString] -> ([S.ByteString],[S.ByteString])
keep !deep xs
    | deep < 1    = ([],xs)
keep deep (!x:xs) = let (!p,d) = keep (deep - S.length x) xs in (x:p,d)
keep _ [] = error "Forgot too much"

------------------------------------------------------------------------------
--                            Breaking Functions                            --
------------------------------------------------------------------------------

-- Ugh! Code duplication ahead!
-- But we want to get the first component lazily, so it's no good to find
-- the first index (if any) and then split.
-- Therefore bite the bullet and copy most of the code of lazySearcher.
-- No need for afterMatch here, fortunately.
lazyBreak ::S.ByteString -> [S.ByteString] -> ([S.ByteString], [S.ByteString])
lazyBreak !pat
  | S.null pat  = \lst -> ([],lst)
  | S.length pat == 1 =
    let !w = S.head pat
        go [] = ([], [])
        go (!str : rest) =
            case S.elemIndices w str of
                []    -> let (pre, post) = go rest in (str : pre, post)
                (i:_) -> if i == 0
                            then ([], str : rest)
                            else ([S.take i str], S.drop i str : rest)
    in go
lazyBreak pat = breaker
  where
    !patLen = S.length pat
    !patEnd = patLen - 1
    !occT   = occurs pat
    !suffT  = suffShifts pat
    !maxLen = maxBound - patLen
    !pe     = patAt patEnd

    {-# INLINE patAt #-}
    patAt !i = unsafeIndex pat i

    {-# INLINE occ #-}
    occ !w = unsafeAt occT (fromIntegral w)

    {-# INLINE suff #-}
    suff !i = unsafeAt suffT i

    breaker lst =
      case lst of
        []    -> ([],[])
        (h:t) ->
          if maxLen < S.length h
            then error "Overflow in BoyerMoore.lazyBreak"
            else seek [] h t 0 patEnd

    seek :: [S.ByteString] -> S.ByteString -> [S.ByteString]
                -> Int -> Int -> ([S.ByteString], [S.ByteString])
    seek !past !str future !offset !patPos
      | strPos < 0 =
        case past of
          [] -> error "not enough past!"
          (h : t) -> seek t h (str : future) (offset + S.length h) patPos
      | strEnd < strPos =
        case future of
          []      -> (foldr (flip (.) . (:)) id past [str], [])
          (h : t) ->
            let !off' = offset - strLen
                (past', !discharge) = keep (-off') (str : past)
            in if maxLen < S.length h
                then error "Overflow in BoyerMoore.lazyBreak (future)"
                else let (pre,post) = seek past' h t off' patPos
                     in (foldr (flip (.) . (:)) id discharge pre, post)
      | patPos == patEnd = checkEnd strPos
      | offset < 0 = matcherN offset patPos
      | otherwise  = matcherP offset patPos
      where
        {-# INLINE strAt #-}
        strAt !i = unsafeIndex str i

        !strLen = S.length str
        !strEnd = strLen - 1
        !maxOff = strLen - patLen
        !strPos = offset + patPos

        checkEnd !sI
          | strEnd < sI = seek past str future (sI - patEnd) patEnd
          | otherwise   =
            case strAt sI of
              !c  | c == pe   ->
                    if sI < patEnd
                      then (if sI == 0
                              then seek past str future (-patEnd) (patEnd - 1)
                              else matcherN (sI - patEnd) (patEnd - 1))
                      else matcherP (sI - patEnd) (patEnd - 1)
                  | otherwise -> checkEnd (sI + patEnd + occ c)

        matcherN !off !patI =
          case strAt (off + patI) of
            !c  | c == patAt patI ->
                  if off + patI == 0
                    then seek past str future off (patI - 1)
                    else matcherN off (patI - 1)
                | otherwise ->
                    let !off' = off + max (suff patI) (patI + occ c)
                    in if maxOff < off'
                        then seek past str future off' patEnd
                        else checkEnd (off' + patEnd)

        matcherP !off !patI =
          case strAt (off + patI) of
            !c  | c == patAt patI ->
                  if patI == 0
                    then let !pre = ([S.take off str | off /= 0])
                             !post = S.drop off str
                         in (foldr (flip (.) . (:)) id past pre, post:future)
                    else matcherP off (patI - 1)
                | otherwise ->
                    let !off' = off + max (suff patI) (patI + occ c)
                    in if maxOff < off'
                        then seek past str future off' patEnd
                        else checkEnd (off' + patEnd)

-- breaking
--
-- Break a string on a pattern. The first component of the result
-- contains the prefix of the string before the first occurrence of the
-- pattern, the second component contains the remainder.
-- The following relations hold:
--
-- > breakSubstringX \"\" str = (\"\", str)
-- > not (pat `isInfixOf` str) == null (snd $ breakSunbstringX pat str)
-- > True == case breakSubstringX pat str of
-- >          (x, y) -> not (pat `isInfixOf` x)
-- >                       && (null y || pat `isPrefixOf` y)

-- | The analogous function for a lazy target string.
--   The first component is generated lazily, so parts of it can be
--   available before the pattern is detected (or found to be absent).
{-# INLINE breakSubstringL #-}
breakSubstringL :: S.ByteString  -- ^ Pattern to break on
                -> L.ByteString  -- ^ String to break up
                -> (L.ByteString, L.ByteString)
                    -- ^ Prefix and remainder of broken string
breakSubstringL pat = breaker . L.toChunks
  where
    lbrk = lazyBreak pat
    breaker strs = let (f, b) = lbrk strs
                   in (L.fromChunks f, L.fromChunks b)
