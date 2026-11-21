import Formalism.SharpRestriction.CuspSpanNormBounds.GramFlagFamilyOfPositive

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  unfold Scale.b Scale.L
  have h1 : 1 ≤ s.x ^ s.eps := Real.one_le_rpow (le_of_lt s.one_lt_alt) s.eps_pos.le
  have h2 := Real.add_one_le_exp (s.x ^ s.eps)
  linarith


section Bound

variable (D : D7) (u u' : D.what₂.Word)

def Pt (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (Cnt.absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))




end Bound

section Fam

def LatticeIdentityGeneric : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F')



end Fam

end Formalism.MainNotions.GramProductBounds

end
