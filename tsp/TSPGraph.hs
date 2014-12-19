
import Graphics.Gloss

imgWidth, imgHeight :: Int
imgWidth  = 600
imgHeight = 600


main :: IO ()
main = display window white (Circle 80)
  where window = InWindow "TSP Visualize" (imgWidth, imgHeight) (10, 10)
