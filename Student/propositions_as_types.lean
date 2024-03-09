inductive BobStudiesAtUVa
| attendClasses
| paidTUition

inductive MaryStudiesAtUVa
| attendClasses
| paidTUition


-- for empty type
inductive MarkoStudiesAtUVa


def neg (α : Type) := α → Empty

example : neg MarkoStudiesAtUVa :=
λ m : MarkoStudiesAtUVa => nomatch m


-- and
inductive BobStudiesAtUVaAndMaryStudiesAtUVa
| and (b : BobStudiesAtUVa) (m : MaryStudiesAtUVa)

def b : BobStudiesAtUVa := BobStudiesAtUVa.paidTUition
def m : MaryStudiesAtUVa := MaryStudiesAtUVa.paidTUition

example: BobStudiesAtUVaAndMaryStudiesAtUVa :=
  BobStudiesAtUVaAndMaryStudiesAtUVa.and b m


-- or
inductive BobStudiesAtUVaOrMaryStudiesAtUVa
| left (b : BobStudiesAtUVa)
| right (m : MaryStudiesAtUVa)

example : BobStudiesAtUVaOrMaryStudiesAtUVa :=
  BobStudiesAtUVaOrMaryStudiesAtUVa.left b
