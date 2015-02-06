
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

  data Clearance : Set where
    Low  : Clearance
    High : Clearance
    God  : Clearance

  record Position : Set where
    constructor pos
    field
      x   : ℕ
      y   : ℕ
      mat : Material
      clr : Clearance

  data _c>_ : Color → Clearance → Set where
    <red>   : ∀ {c} → c c> Low
    <green> : Green c> High

  data _follows_ : Position → Position → Set where
    stay  : ∀ {x y} → pos x y gas Low follows pos x y gas Low
    next  : ∀ {c cl x y}{{_ : c c> cl}} →
            pos (suc x) y gas Low follows pos x y gas cl
    back  : ∀ {c cl x y}{{_ : c c> cl}} →
            pos x y gas Low follows pos (suc x) y gas cl
    -- jump  : ∀ {x y} → pos x (suc y) gas High follows pos x y gas Low
    fall  : ∀ {cl x y} → pos x y gas cl follows pos x (suc y) gas High


  infixr 5 _↠⟨_⟩_
  data Path (Koopa : KoopaTroopa Color) : Position → Position → Set where
    []  : ∀ {p} → Path Koopa p p
    _↠⟨_⟩_ : {q r : Position} → (p : Position) → q follows p
                → (qs : Path Koopa q r) → Path Koopa p r

  ex_path : Path (Red KT) (pos 0 0 gas Low) (pos 0 0 gas Low)
  ex_path = pos 0 0 gas Low ↠⟨ next {Red} ⟩
            pos 1 0 gas Low ↠⟨ back ⟩
            pos 0 0 gas Low ↠⟨ stay ⟩ []

  matToPosVec : {n : ℕ} → Vec Material n → Vec Material n → ℕ → ℕ →
                   Vec Position n
  matToPosVec []           []        _ _ = []
  matToPosVec (mat ∷ mats) (under ∷ unders) x y =
    pos x y mat cl ∷ matToPosVec mats unders (x + 1) y
      where
        clearance : Material → Material → Clearance
        clearance gas   gas   = High
        clearance gas   solid = Low
        clearance solid _     = God
        cl = clearance mat under

  matToPosVecs : {w h : ℕ} → Vec (Vec Material w) h → Vec (Vec Position w) h
  matToPosVecs []                   = []
  matToPosVecs (_∷_ {y} mats matss) = matToPosVec mats mats 0 y ∷ matToPosVecs matss

  matsToMat : {w h : ℕ} → Vec (Vec Material w) h → Matrix Position w h
  matsToMat matss = Mat (matToPosVecs matss)

  □ : Material
  □ = gas
  ■ : Material
  ■ = solid
  example_level : Matrix Position 10 7
  example_level = matsToMat (
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (■ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ ■ ∷ []) ∷ 
    (■ ∷ ■ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ []) ∷ [])
