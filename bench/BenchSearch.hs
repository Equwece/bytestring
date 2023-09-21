{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Test.Tasty.Bench
import qualified System.Random as SR
import Control.Monad (replicateM)
import Data.Word (Word8)
import Data.ByteString.Lazy (pack, empty)
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString.Lazy.Internal.BoyerMoore as BM
import qualified Data.ByteString.Lazy.Internal.Search as SE
import GHC.Int (Int64)

genByteStrToSearch :: Int -> Int -> IO (L.ByteString, L.ByteString) 
genByteStrToSearch patLen strLen = do
  sStr <- pack <$> replicateM strLen (SR.randomRIO (0 :: Word8, 255 :: Word8))
  let patOffsetBound = strLen - patLen
  if patOffsetBound < 0
    then return (empty, empty)
    else do
      randOffset <- SR.randomRIO (0, patOffsetBound)
      let sPat = L.take (fromIntegral $ strLen - randOffset) . L.drop (fromIntegral randOffset) $ sStr
      return (sPat, sStr)
      

main :: IO ()
main = do
  searchOrigin <- L.readFile "./benchText.txt"
  print $ L.length searchOrigin
  defaultMain
    [ bgroup "breakSubstring"
      [ bench "New Booyer Moore" $ nf (SE.searchBoyerMoore "some search string") searchOrigin
      , bench "Naive" $ nf (L.breakSubstring "some search string") searchOrigin
      , bench "Stringsearch's BM" $ nf (BM.breakSubstringL "some search string") searchOrigin
      ]
    ]
