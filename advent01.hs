import Control.Applicative
import Data.Maybe (mapMaybe)
import System.IO

sums :: [Int] -> [(Int, Int, Int)]
sums l = do
  a <- l
  b <- l
  return (a, b, a + b)

sums3 :: [Int] -> [(Int, Int, Int, Int)]
sums3 l = do
  a <- l
  b <- l
  c <- l
  return (a, b, c, a + b + c)


inSolution :: (Int, Int, Int) -> Maybe Int
inSolution (a, b, sum) =
  if sum == 2020 then Just (a * b) else Nothing

inSolution3 :: (Int, Int, Int, Int) -> Maybe Int
inSolution3 (a, b, c, sum) =
  if sum == 2020 then Just (a * b * c) else Nothing

solutionA :: [Int] -> Int
solutionA = head . mapMaybe inSolution . sums

solutionB :: [Int] -> Int
solutionB = head . mapMaybe inSolution3 . sums3

main :: IO ()
main = do
  input <- (((map read . lines) <$> getContents) :: IO [Int])
  putStrLn $ show $ solutionA input
  putStrLn $ show $ solutionB input
  return ()
