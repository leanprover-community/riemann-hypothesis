import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RosatiNormLEOfStarNormLE

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

def TateCharPolySt : Prop := EndCharPolySt


end GlobalTheory.Published

namespace GlobalTheory.TateCharPoly

open ThetaDetCompare ThetaCoord

variable {K : Type} [Field K] {P : PolAV (Sp K)}

def IsCharPoly (P : PolAV (Sp K)) (ψ : P.A ⟶ P.A) (χ : Polynomial ℤ) : Prop :=
  ∀ l r : ℕ, l.Prime → (l : K) ≠ 0 → ∀ y, Frame P (l ^ r) y →
    ∀ B : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ r)), Rep y ψ B →
      B.charpoly = χ.map (Int.castRingHom (ZMod (l ^ r)))


variable [IsAlgClosed K]

theorem IsCharPoly.unique (hL : Laws) {ψ : P.A ⟶ P.A} [IsMonHom ψ] {χ χ' : Polynomial ℤ} (h : IsCharPoly P ψ χ)
    (h' : IsCharPoly P ψ χ') : χ = χ' :=
  Polynomial.ext fun n => int_eq_of_frames hL P fun l r hl hK y hy => by
    obtain ⟨B, hB⟩ := hy.exists_rep ψ
    simpa using congrArg (·.coeff n) ((h l r hl hK y hy B hB).symm.trans (h' l r hl hK y hy B hB))


end GlobalTheory.TateCharPoly
