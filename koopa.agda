{-

    Verified Koopa Troopa Movement
             Toon Nolten

-}

module koopa where
  open import Data.Nat
  open import Data.Fin renaming (_+_ to _F+_)
  open import Data.List
  open import Data.Vec renaming (map to vmap; lookup to vlookup)

  module Matrix where
    data Matrix (A : Set) : ℕ → ℕ → Set where
      Mat : {w h : ℕ} → Vec (Vec A w) h → Matrix A w h

    lookup : ∀ {w h} {A : Set} → Fin h → Fin w → Matrix A w h → A
    lookup row column (Mat rows) = vlookup column (vlookup row rows)
  open Matrix

  data Color : Set where
    Green : Color
    Red : Color

  data KoopaTroopa Color : Set where
    _KT : Color → KoopaTroopa Color

  data Material : Set where
    gas    : Material
    -- liquid : Material
    solid  : Material

  record Position : Set where
    constructor pos
    field
      x   : ℕ
      y   : ℕ
      mat : Material

  data _follows_ : Position → Position → Set where
    stay  : ∀ {p} → p follows p
    next  : ∀ {x y mat} → pos (suc x) y mat follows pos x y mat
    back  : ∀ {x y mat} → pos x y mat follows pos (suc x) y mat
    -- jump  : ∀ {x y mat} → pos x (suc y) mat follows pos x y mat
    fall  : ∀ {x y mat} → pos x y mat follows pos x (suc y) mat


  infixr 5 _↠⟨_⟩_
  data Path (Koopa : KoopaTroopa Color) : Position → Position → Set where
    []  : ∀ {p} → Path Koopa p p
    _↠⟨_⟩_ : {q r : Position} → (p : Position) → q follows p
                → (qs : Path Koopa q r) → Path Koopa p r

  ex_path : Path (Red KT) (pos 0 0 solid) (pos 0 0 solid)
  ex_path = pos 0 0 solid ↠⟨ next ⟩
            pos 1 0 solid ↠⟨ back ⟩
            pos 0 0 solid ↠⟨ stay ⟩ []

  matToPosVec : {n : ℕ} → Vec Material n → ℕ → ℕ → Vec Position n
  matToPosVec []           _ _ = []
  matToPosVec (mat ∷ mats) x y = pos x y mat ∷ matToPosVec mats (x + 1) y

  matToPosVecs : {w h : ℕ} → Vec (Vec Material w) h → Vec (Vec Position w) h
  matToPosVecs []                   = []
  matToPosVecs (_∷_ {y} mats matss) = matToPosVec mats 0 y ∷ matToPosVecs matss

  matToMat : {w h : ℕ} → Vec (Vec Material w) h → Matrix Position w h
  matToMat matss = Mat (matToPosVecs matss)

  □ : Material
  □ = gas
  ■ : Material
  ■ = solid
  example_level : Matrix Position 10 7
  example_level = Mat (matToPosVecs (
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (■ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ ■ ∷ []) ∷ 
    (■ ∷ ■ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ []) ∷ []))

