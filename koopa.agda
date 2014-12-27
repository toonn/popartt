{-

    Verified Koopa Troopa Movement
             Toon Nolten

-}

module koopa where
open import Data.Nat

data Color : Set where
  Green : Color
  Red : Color

data KoopaTroopa Color : Set where
  _KT : Color → KoopaTroopa Color

record Position : Set where
  constructor pos
  field
    x : ℕ
    y : ℕ

data _follows_ : Position → Position → Set where
  still : ∀ {p} → p follows p
  next  : ∀ {x y} → pos (suc x) y follows pos x y
  back  : ∀ {x y} → pos x y follows pos (suc x) y
  -- jump  : ∀ {x y} → pos x (suc y) follows pos x y
  fall  : ∀ {x y} → pos x y follows pos x (suc y)


data Path (Koopa : KoopaTroopa Color) : Position → Position → Set where
  []  : ∀ {p} → Path Koopa p p
  _↠[_]_ : {q r : Position} → (p : Position) → q follows p
           → (qs : Path Koopa q r) → Path Koopa p r

ex_path : Path (Red KT) (pos 0 0) (pos 0 0)
ex_path = pos 0 0 ↠[ next ] (pos 1 0 ↠[ back ] [])
