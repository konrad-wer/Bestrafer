module CommonUtils where

pair :: (a -> b, a -> c) -> a -> (b, c)
pair (f, g) x = (f x, g x)

cross :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
cross f g = pair (f . fst, g . snd)
