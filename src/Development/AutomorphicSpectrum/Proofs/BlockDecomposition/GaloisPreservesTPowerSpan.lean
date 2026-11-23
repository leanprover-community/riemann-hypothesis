module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
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

@[expose] public section

set_option autoImplicit false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatGal

private theorem galBdRHom_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p) (x : BDeRhamPlus (normInteger ℂ_[p]) p)
    (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)) :
    galBdRHom σ x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  intro hu
  apply hx
  have h1 : galBdRHom σ⁻¹ (galBdRHom σ x) = x := by
    rw [← RingHom.comp_apply, ← galBdRHom_mul, inv_mul_cancel, galBdRHom_one, RingHom.id_apply]
  rw [← h1]
  exact hu.map _

theorem span_tBdR_pow_le_comap (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (k : ℕ) (g : K.fixingSubgroup) :
    Ideal.span {tBdR l ^ k} ≤ (Ideal.span {tBdR l ^ k}).comap (Lat.gP l g) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  have ht : Lat.gP l g (tBdR l) ∈ Ideal.span {tBdR l} := by
    rw [← maximalIdeal_eq_span_tBdR]
    exact galBdRHom_mem_maximalIdeal _ _ (by rw [maximalIdeal_eq_span_tBdR]; exact Ideal.mem_span_singleton_self _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ht
  rw [← hc, mul_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.LatGal
