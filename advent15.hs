import Control.Monad (sequence)
import Debug.Trace

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text.Read as TR

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

turn :: Int -> Int -> IntMap Int -> [Int]
turn prev t map =
  let prev' =
        case IntMap.lookup prev map of
          Just t2 -> (t - 1) - t2
          Nothing -> 0
  in prev':(turn prev' (t + 1) (IntMap.insert prev (t - 1) map))

game_seq :: [Int] -> [Int]
game_seq init = init ++ turn (last init) (length init + 1) map
  where map = IntMap.fromList (zip init [1..])

main :: IO ()
main = do
  input <- TIO.getLine
  let init = either error (map fst) $ sequence $ map (TR.decimal :: TR.Reader Int) $
            T.splitOn (T.pack ",") input :: [Int]
  let seq = game_seq init
  let soln_a = seq !! 2019
  putStrLn $ "Part a: " ++ show soln_a
  let soln_b = seq !! (30000000 - 1)
  putStrLn $ "Part b: " ++ show soln_b
