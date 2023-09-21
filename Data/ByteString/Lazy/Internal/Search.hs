{-# LANGUAGE BangPatterns #-}

-- Copyright (c)2010, Daniel Fischer
--           (c) Chris Kuklewicz

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

module Data.ByteString.Lazy.Internal.Search
  (
    getBadCharTable,
    patAt,
    getGoodSuffixTable,

  searchBoyerMoore)
  where

import qualified Data.ByteString.Array as DA
import Data.ByteString.Unsafe (unsafeIndex)

import qualified Data.ByteString.Internal.Type as S
import qualified Data.ByteString as S
import qualified Data.ByteString.Lazy as L
import Control.Monad (when)


{-# INLINE patAt #-}
patAt :: S.ByteString -> Int -> Int
patAt pat i = fromIntegral (unsafeIndex pat i)

getBadCharTable :: S.ByteString -> DA.Array
getBadCharTable pat = DA.run $ do
  let !patEndInd = S.length pat - 1
      pA = patAt pat
  ar <- DA.newFilled 256 1
  let go !i
          | i == patEndInd   = return ar
          | otherwise     = do
              DA.unsafeWrite ar (pA i) (fromIntegral i)
              go (i + 1)
  go 0

getGoodSuffixTable :: S.ByteString -> DA.Array
getGoodSuffixTable pat = DA.run $ do
  let patLen = S.length pat
      pA i = if i >= 0 then patAt pat i else patAt pat (patLen + i)
  borderPosArr <- DA.newFilled (patLen + 1) 0
  shiftArr <- DA.newFilled (patLen + 1) 0
  DA.unsafeWrite borderPosArr patLen (fromIntegral $ patLen + 1)
  let processStrongSuffix !i !j
        | i <= 0 = return ()
        | otherwise =  do
            (nI, nJ) <- go i j
            DA.unsafeWrite borderPosArr (nI - 1) (fromIntegral $ nJ - 1)
            processStrongSuffix (nI - 1) (nJ - 1)
      go !i !j
        | j > patLen = return (i, j)
        | pA (i - 1) == pA (j - 1) = return (i, j)
        | otherwise = do
            precedingChar <- DA.unsafeIndexM shiftArr j
            when (precedingChar == 0) (DA.unsafeWrite shiftArr j (fromIntegral $ j - i))
            newJ <- DA.unsafeIndexM borderPosArr j
            go i (fromIntegral newJ)
  processStrongSuffix patLen (patLen + 1)
  let processSecondRule !i !j
        | i == patLen + 1 = return ()
        | otherwise = do
            currentChar <- DA.unsafeIndexM shiftArr i
            when (currentChar == 0) (DA.unsafeWrite shiftArr i j)
            if i == fromIntegral j
              then do
                newJ <- DA.unsafeIndexM borderPosArr (fromIntegral j)
                processSecondRule (i + 1) newJ
              else processSecondRule (i + 1) j
  j <- DA.unsafeIndexM borderPosArr 0
  processSecondRule 0 j
  return shiftArr

searchBoyerMoore :: S.ByteString -> L.ByteString -> Maybe Int
searchBoyerMoore pat = search 0
  where
    patLen = S.length pat
    badCharTable = getBadCharTable pat
    goodSuffTable = getGoodSuffixTable pat

    search :: Int -> L.ByteString -> Maybe Int
    search shiftInd srcString
      | shiftInd + patLen > srcLen = Nothing
      | otherwise = case go (patLen - 1) of
          (True, _) -> Just shiftInd
          (False, newShift) -> search (shiftInd + newShift) srcString
      where
        srcLen = fromIntegral . L.length $ srcString :: Int
        go patShift
          | patShift < 0 = (True, 0)
          | S.index pat patShift /= L.index srcString (fromIntegral . (+) shiftInd $ patShift) = (False, getNewShift)
          | otherwise = go (patShift - 1)
          where
            badCharShift
              = (-) patShift
                  . fromIntegral
                  . DA.unsafeIndex badCharTable
                  . fromIntegral
                  . L.index srcString $ (fromIntegral . (+) shiftInd $ patShift)
            goodSuffShift = fromIntegral $ DA.unsafeIndex goodSuffTable (patShift + 1) :: Int
            getNewShift = foldl (flip max) 0 [badCharShift, goodSuffShift, 1]
