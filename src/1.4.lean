
/-
Define a structure named RectangularPrism that
contains the height, width, and depth of a rectangular prism,
each as a Float.
-/
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

/-
Define a function named volume 
: RectangularPrism → Float that computes the volume of a
rectangular prism.
-/
def volume (rp : RectangularPrism) : Float :=
  rp.depth * rp.height * rp.depth

/-
Define a structure named Segment that represents a line
segment by its endpoints, and define a function 
length : Segment → Float that computes the length of a line
segment. Segment should have at most two fields.
-/
structure Segment where
  p1 : Prod Float Float
  p2 : Prod Float Float

def length (s : Segment) : Float :=
  (Float.sqrt ((Float.pow (s.p1.fst - s.p2.fst) 2) +
              (Float.pow (s.p1.snd - s.p2.snd) 2)))

#eval length ⟨⟨0,0⟩,⟨1,1⟩⟩

/-
Which names are introduced by the declaration of RectangularPrism?
-/

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

/-
Which names are introduced by the following declarations
of Hamster and Book? What are their types?
-/

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Hamster
#check Hamster.mk
#check Hamster.name
#check Book
--#check Book.mk --does not exist bc custom cons
-- specified via "makeBook ::""
#check Book.makeBook
#check Book.title
#check Book.author
#check Book.price