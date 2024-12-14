/- @file Notes/Chapter1/Section4.lean
 - @src https://lean-lang.org/functional_programming_in_lean/getting-to-know/structures.html
 -/

/- SECTION: Structures -/

-- Product type # Math: \texttt{Float} \times \texttt{Float}
--  with named fields `x` and `y`.
structure Point where
  x : Float
  y : Float
deriving Repr  -- This is the typeclass that `#eval` uses to render computed expressions
/- This introduces the names:
`Point.mk : Float → Float → Float` constructor
`Point.x : Point → Float` left destructor
`Point.y : Point → Float` right destructor
-/
#eval Point.mk 69 420
#eval ({ x := 69, y := 420 } : Point) -- Record syntax with explicit type pinned down
#eval { x := 69, y := 420 : Point } -- shorthand for including an explicit type
/- Note that due to the following syntax rule
    For `t : T` and `f : T → X`, we have the shortchand `t.f := f t`
  we can write `p.x` to compute to `Point.x p` which extracts `p`'s `x` coordinate.
  This binds more tightly than function application.
-/
#eval { x := 69, y := 420 : Point }.x
-- You can use the aforementioned rule to make `String.append` look less shit:
#eval "Hello ".append "world"
#eval "Hello ".append ("my ".append "world") -- you've still gotta do this shit though
-- You can also do dumbass shit like this:
#eval (2.0).sqrt -- lol this is cursed af   -- NOTE: `Float.sqrt : Float → Float`

def addPoints (p : Point) (q : Point) : Point :=
  { x := p.x + q.x
  , y := p.y + q.y
  : Point }
#eval addPoints {x:=1,y:=2} {x := 69, y := 420}
#check (addPoints)

def distance (p q : Point) : Float :=
  Float.sqrt $ (p.x - q.x)^2 + (p.y - q.y)^2  -- has the Haskell `$` too
#eval distance { x := 0, y := 0 } { x := 420, y := 69 }


-- You can override the constructor name like this
structure Point3D where
  makePoint3D:: -- `Point3D.makePoint3D` is now the constructor name
    x : Float
    y : Float
    z : Float
#check Point3D.makePoint3D
-- #check Point3D.mk       -- doesn't exist
#eval { x := 1, y := 2 : Point } -- need explicit type information due to colliding structure fields `x` in `Point` and `Point3D`



/- SECTION: Updating structures -/

-- This syntax is cool. It does what you think it does.
#eval (
  let p := { x := 69, y := 420 : Point }
  ; -- Lean's `;` is Haskell's `in`
    { p with x := 420 } -- this is the cool bit
)



/- SECTION: Exercises -/

structure RectangularPrism where
  length : Float
  width  : Float
  depth  : Float
/- Introduces names:
    `RectangularPrism.mk     : Float → Float → Float → RectangularPrism`
    `RectangularPrism.length : RectangularPrism → Float`
    `RectangularPrism.width  : RectangularPrism → Float`
    `RectangularPrism.depth  : RectangularPrism → Float`
-/

def volume (r : RectangularPrism) : Float :=
  r.length * r.width * r.depth

structure Segment where
  source : Point
  target : Point
deriving Repr

def length (s : Segment) : Float :=
  distance s.source s.target
