
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

def volume (rp : RectangularPrism) : Float :=
  rp.depth * rp.height * rp.depth

structure Segment where
  p1 : Prod Float Float
  p2 : Prod Float Float

def length (s : Segment) : Float :=
  (Float.sqrt ((Float.pow (s.p1.fst - s.p2.fst) 2) +
              (Float.pow (s.p1.snd - s.p2.snd) 2)))

#eval length ⟨⟨0,0⟩,⟨1,1⟩⟩

/-
Names introduced by RectangularPrism
RectangularPrism
RectangularPrism.mk
RectangularPrism.height
RectangularPrism.width
RectangularPrism.depth
-/
#check RectangularPrism
#check RectangularPrism.mk
#check RectangularPrism.height
#check RectangularPrism.width
#check RectangularPrism.depth