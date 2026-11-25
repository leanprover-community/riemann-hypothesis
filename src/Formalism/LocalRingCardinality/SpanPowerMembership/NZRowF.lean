module

public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.CodeRecordDiscriminantLevel
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZColC
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowC
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Pure

variable {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
  (hstar : ∀ z, σ (star z) = starRingEnd ℂ (σ z)) {n : ℕ}
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V)


end Pure

section Sharp

variable (D : D7)

theorem sharp_downTo (μ) (j : ℕ) : (RowSide.sharp D).downTo μ j = D.what₂.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    show ((RowSide.sharp D).downTo μ j).comp (D.what₂.io μ j) = (D.what₂.downTo μ j).comp (D.what₂.io μ j)
    rw [ih]; rfl

theorem sharp_iota (μ) : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
  unfold RowSide.iota Rows.Data.iota
  rw [sharp_downTo]; rfl

end Sharp


end Formalism.BasicNotions.Examples₂.NZ
