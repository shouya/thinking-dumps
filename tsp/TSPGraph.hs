module TSPGraph (
  presentUI
  ) where

import Graphics.Gloss
import TSPLib
import Data.Monoid
import Data.Functor
import Control.Arrow ((***))


imgWidth, imgHeight :: Int
imgWidth  = 600
imgHeight = 600


main :: IO ()
main = do
  (nodes, edges) <- parseInput
  presentUI nodes edges

presentUI :: [Node] -> [Edge] -> IO ()
presentUI nodes edges =
  let window = InWindow "TSP Visualize" (imgWidth, imgHeight) (10, 10)
      (halfW, halfH) = (fromIntegral (-imgWidth)/2, fromIntegral (-imgHeight)/2)
      translatedPic  = scale 0.9 (-0.9) $ translate halfW halfH pic
      (xrng, yrng)   = (xRange nodes, yRange nodes)
      pic = paintNodes nodes xrng yrng <>
            paintEdges edges xrng yrng
    in display window white translatedPic

scaleVal :: (Fractional a) => (a, a) -> a -> a -> a
scaleVal (xmin, xmax) scl x = scl * (x - xmin) / (xmax - xmin)

tupleFromIntegral :: (Num c, Num d, Integral a, Integral b) =>
                     (a, b) -> (c, d)
tupleFromIntegral = fromIntegral *** fromIntegral

scaleVal' :: (Int, Int) -> Int -> Int -> Float
scaleVal' rng scl = scaleVal fltrng fltscl . fromIntegral
  where fltrng = tupleFromIntegral rng
        fltscl = fromIntegral scl

scaleTuple :: (Int, Int) -> (Int, Int) -> Int -> Int ->
              (Int, Int) -> (Float, Float)
scaleTuple xrng yrng xmax ymax = scaleX *** scaleY
  where scaleX = scaleVal' xrng xmax
        scaleY = scaleVal' yrng ymax

paintNodes :: [Node] -> (Int,Int) -> (Int,Int) -> Picture
paintNodes []  _ _  = blank
paintNodes [_] _ _  = blank
paintNodes ns xr yr = pictures $ zipWith paintNode [0..] ns
  where scalePoint = scaleTuple xr yr imgWidth imgHeight
        getcolor n = if n == 0 then red else black
        paintNode n node = uncurry translate (scalePoint node) $
                           color (getcolor n) $
                           circle 5



paintEdges :: [Edge] -> (Int,Int) -> (Int,Int) -> Picture
paintEdges []  _ _  = blank
paintEdges [_] _ _  = blank
paintEdges ns xr yr = pictures $ map paintEdge ns
  where scalePoint = scaleTuple xr yr imgWidth imgHeight
        paintEdge (p1, p2) = color blue $ line [scalePoint p1, scalePoint p2]



parseInput :: IO ([Node], [Edge])
parseInput = do
  (cfg:raw) <- lines <$> getContents
  let [nn, _] = map read $ words cfg
      rest = map (map read . words) raw
      (ns, es) = splitAt nn rest
      nodes = map (\[a,b] -> (a,b)) ns
      edges = map (\[a,b,c,d] -> ((a,b), (c,d))) es
    in return (nodes, edges)
