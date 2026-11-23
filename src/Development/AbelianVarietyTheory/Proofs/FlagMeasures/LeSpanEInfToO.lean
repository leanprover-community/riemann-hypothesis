module

import Formalism.LocalToGlobal.IndefiniteReal.MemSpanOfSmulMem
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField

namespace GlobalTheory.SpanInfDenominators

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (Λ : Submodule (𝓞 E) V) (x : V)
    (hx : x ∈ Submodule.span E (Λ : Set V)) : ∃ c : 𝓞 E, c ≠ 0 ∧ c • x ∈ Λ := by
  apply Formalism.IndefR.LatticeTransfer.Lat.exists_smul_mem <;> assumption

theorem le_spanE_inf_toO {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E}
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsFullLattice E Λ) (U : Submodule E S.V) :
    U ≤ Formalism.MainNotions.S.Lat.spanE S (Λ ⊓ Formalism.MainNotions.S.Lat.toO S U) := by
  intro x hx
  have hxs : x ∈ Submodule.span E (Λ : Set S.V) := by
    rw [hΛ.span_eq_top]
    trivial
  obtain ⟨c, hc, hcx⟩ := exists_smul_mem Λ x hxs
  have hcU : c • x ∈ U := by
    rw [← algebraMap_smul E c x]
    exact U.smul_mem _ hx
  have hmem : c • x ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S U := Submodule.mem_inf.2 ⟨hcx, hcU⟩
  have hc' : algebraMap (𝓞 E) E c ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)]
  have hx' : x = (algebraMap (𝓞 E) E c)⁻¹ • (c • x) := by
    rw [← algebraMap_smul E c x, smul_smul, inv_mul_cancel₀ hc', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.SpanInfDenominators
