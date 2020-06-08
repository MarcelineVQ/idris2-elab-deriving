module Util

export
catMaybes : List (Maybe a) -> List a
catMaybes z = foldr (\m,f => maybe f (\x => (x ::) . f) m) id z []

export
unzip : List (a,b) -> (List a, List b)
unzip = foldr (\(x,y),(xs,ys) => (x :: xs, y :: ys)) ([],[])
