module DeepRegion where

type Point  = (Double,Double)
type Radius = Double

magnitude :: Point -> Double
magnitude (x,y) = sqrt (x^2 + y^2)

data Region = Circle Radius
            | Intersect Region Region
            | Outside   Region
            | Union     Region Region

circle  r = Circle    r
outside r = Outside   r
r1 /\ r2  = Intersect r1 r2
r1 \/ r2  = Union     r1 r2

p `inRegion` (Circle  r)       = magnitude p <= r
p `inRegion` (Outside r)       = not (p `inRegion` r)
p `inRegion` (Intersect r1 r2) = p `inRegion` r1 && p `inRegion` r2
p `inRegion` (Union     r1 r2) = p `inRegion` r1 || p `inRegion` r2

annulus :: Radius -> Radius -> Region
annulus r1 r2 = outside (circle r1) /\ (circle r2)
