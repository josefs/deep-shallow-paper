module ShallowRegion where

type Point  = (Double,Double)
type Radius = Double

magnitude :: Point -> Double
magnitude (x,y) = sqrt (x^2 + y^2)

type Region = Point -> Bool

p `inRegion` r = r p
circle  r      = \p -> magnitude p <= r
outside r      = \p -> not (r p)
r1 /\ r2       = \p -> r1 p && r2 p
r1 \/ r2       = \p -> r1 p || r2 p

annulus :: Radius -> Radius -> Region
annulus r1 r2 = outside (circle r1) /\ (circle r2)

