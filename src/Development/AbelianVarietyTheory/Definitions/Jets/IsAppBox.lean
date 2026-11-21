import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.BoxApp

def IsApp {R : Type} [CommRing R] [IsDomain R] {D D₂ D' : DegPre R} {n₁ n₂ : ℕ} (pD₂ : IsPowDeg D₂ D n₂)
    (pD : IsPowDeg D' D (n₁ + n₂)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (a : Fin n₁ → Fam D F k) (sb : Fam D₂ F k) (S : Fam D' F k) : Prop :=
  ∃ (l : ℕ) (c : Fin l → F) (u : Fin l → Fin n₂ → Fam D F k) (S₂ : Fin l → Fam D₂ F k) (S' : Fin l → Fam D' F k),
    (∀ j, IsBoxFam pD₂ F k (S₂ j) (u j)) ∧ (∀ j, IsBoxFam pD F k (S' j) (Fin.append a (u j))) ∧
      sb = ∑ j, c j • S₂ j ∧ S = ∑ j, c j • S' j


end GlobalTheory.BoxApp
