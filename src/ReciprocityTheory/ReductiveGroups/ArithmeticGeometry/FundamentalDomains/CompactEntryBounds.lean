module

import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticLatticeForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace CompactEntryBounds

open Matrix NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  apply GlobalTheory.FlagMahler.hermC_expand

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w :=
  GlobalTheory.FlagMahler.hermC_stab X hγ τ u w

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ X.Gm (γ.map τ * Y) = gram τ X.Gm Y :=
  GlobalTheory.FlagMahler.gram_stab X hγ τ Y

def Kset (R : ℝ) : Set (Frame X.Ψ r) :=
  {w | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat w τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ a c, ‖w τ a c‖ ≤ R}

theorem det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 :=
  GlobalTheory.FlagMahler.det_ne_of_gram X hg

end CompactEntryBounds

end ReciprocityTheory.ChartRestriction.G.FD
