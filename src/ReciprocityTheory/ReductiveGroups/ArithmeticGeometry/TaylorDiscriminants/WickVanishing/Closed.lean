module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSCCols
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionSecondOfCommute
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpConjConnectionIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaHCols
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionKillsSeries

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Closed

theorem lemma_H_columns : ReciprocityTheory.ChartRestriction.G.TB.LemmaHColsSt :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.lemmaHCols_of Val.harmonic_value_integral ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_second_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_kills_series

theorem symmetric_canonical_gauge : ReciprocityTheory.ChartRestriction.G.TB.SCSt :=
  ReciprocityTheory.ChartRestriction.G.TB.SCPf.sc_of ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_first_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_second_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_kills_series

private theorem prod_mem_pow_of_mem_pow_of_sum_le {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (J : Submodule R A) (hJ : (1 : A) ∈ J) {n : ℕ} (x : Fin n → A) (a : Fin n → ℕ) (e : ℕ)
    (hx : ∀ b, x b ∈ J ^ a b) (ha : ∑ b, a b ≤ e) : ∏ b, x b ∈ J ^ e := by
  have hprod : ∀ s : Finset (Fin n), ∏ b ∈ s, x b ∈ J ^ (∑ b ∈ s, a b) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.one_le.mp le_rfl
    · intro i t hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
      exact Submodule.mul_mem_mul (hx i) ih
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le ha
  have h1 : (1 : A) ∈ J ^ c := by
    first
      | simpa using Submodule.pow_mem_pow J hJ c
      | simpa using Submodule.pow_mem_pow hJ c
  have hm := Submodule.mul_mem_mul (hprod Finset.univ) h1
  rwa [mul_one, ← pow_add, ← hc] at hm

theorem scaled_connection_columns : ReciprocityTheory.ChartRestriction.G.TB.SCColsSt :=
  by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hB w0 hw0 m ι π _ _ _ c s ξh ψ hξ hψ hp1 hp2 hp3 n P hPc e he f hf
  refine Submodule.sum_mem _ (fun mo _ => ?_)
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp (hPc mo)
  rw [← hr, ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (prod_mem_pow_of_mem_pow_of_sum_le J hJ1 _ _ e (fun b => ?_) (he mo ‹_›))
  refine symmetric_canonical_gauge R d O k hRQ J hJ1 B h hB w0 hw0 m ι π c s ξh ψ hξ hψ hp1 hp2 hp3 _ ?_ _ ?_ (f b) (hf b)
  · intro x
    classical
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro x hx
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hx)]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Closed
