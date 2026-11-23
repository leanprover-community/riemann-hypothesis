module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.UnitaryGroupMassFormula.TBIdemDen

open ReciprocityTheory.ChartRestriction.G.TB NumberField TensorProduct

theorem idemEval : IdemEvalSt := by
  intro E _ _ C _ _ _ ι _ _ b τ σ
  classical
  have hev : evAt σ (idemOf b τ) = ∑ i, σ (trDual b i) * τ (b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evAt, idemOf, map_sum, Algebra.TensorProduct.productMap_apply_tmul,
      AlgHom.id_apply, RingHom.toRatAlgHom_apply]
  rw [hev]
  have hexp : ∀ y : E, y = ∑ i, Algebra.trace ℚ E (y * b i) • trDual b i := by
    intro y
    conv_lhs => rw [← (trDual b).sum_repr y]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [trDual, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  set σ' : E →ₐ[ℚ] C := σ.toRatAlgHom with hσ'
  set τ' : E →ₐ[ℚ] C := τ.toRatAlgHom with hτ'
  let c : (E →ₐ[ℚ] C) → C := fun φ => ∑ i, φ (b i) * σ' (trDual b i)
  have hc : ∀ y : E, ∑ φ : E →ₐ[ℚ] C, c φ * φ y = σ' y := by
    intro y
    calc ∑ φ : E →ₐ[ℚ] C, c φ * φ y
        = ∑ i, σ' (trDual b i) * ∑ φ : E →ₐ[ℚ] C, φ (y * b i) := by
          simp only [c, Finset.sum_mul, Finset.mul_sum, map_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun φ _ => ?_
          ring
      _ = ∑ i, σ' (Algebra.trace ℚ E (y * b i) • trDual b i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← trace_eq_sum_embeddings C, Algebra.smul_def, map_mul σ', AlgHom.commutes]
          ring
      _ = σ' y := by rw [← map_sum, ← hexp]
  have hinj : Function.Injective (fun φ : E →ₐ[ℚ] C => (φ : E →* C)) := by
    intro φ ψ h
    ext x
    exact DFunLike.congr_fun h x
  have hli := (linearIndependent_monoidHom E C).comp _ hinj
  have hz := Fintype.linearIndependent_iff.1 hli (fun φ => c φ - if φ = σ' then 1 else 0) (by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply,
      MonoidHom.coe_coe, sub_mul, Finset.sum_sub_distrib, hc y, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self])
  have key := hz τ'
  rw [sub_eq_zero] at key
  have hiff : (τ' = σ') ↔ (σ = τ) := by
    constructor
    · intro h
      ext x
      exact (DFunLike.congr_fun h x).symm
    · intro h
      rw [hτ', hσ', h]
  calc ∑ i, σ (trDual b i) * τ (b i) = c τ' := by
        simp only [c]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_comm]
        rfl
    _ = _ := by
        rw [key]
        exact if_congr hiff rfl rfl

end PI.UnitaryGroupMassFormula.TBIdemDen
