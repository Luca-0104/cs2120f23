/-!
a truth table

| P | Q | P → Q |
|---|---|-------|
| T | T |   T   |
| T | F |   F   |
| F | T |   T   |
| F | F |   T   |

-/

#check Empty

def e2e : Empty → Empty
| e => e

def n2e : Nat → Empty
| n => _
