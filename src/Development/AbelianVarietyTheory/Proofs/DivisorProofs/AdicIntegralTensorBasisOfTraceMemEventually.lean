module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem isIntB_of_trace_mem :
    ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ E : v.adicCompletion ℚ ⊗[ℚ] L,
      (∀ i, Algebra.trace (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)
          (E * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] bL i)) ∈ v.adicCompletionIntegers ℚ) →
        IsIntB v bL E := by
  intro L _ _ κ bL
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have hd : Algebra.discr ℚ bL ≠ 0 := Algebra.discr_not_zero_of_basis ℚ bL
  obtain ⟨S, hS⟩ := exists_finset_algebraMap_mem
    (insert (Algebra.discr ℚ bL)⁻¹
      (Finset.univ.image fun p : κ × κ => Algebra.trace ℚ L (bL p.1 * bL p.2)))
  refine ⟨S, fun v hv E hE => ?_⟩
  set Q := v.adicCompletion ℚ
  let B := Algebra.TensorProduct.basis Q bL
  have hB : ∀ i, B i = (1 : Q) ⊗ₜ[ℚ] bL i := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have htr : ∀ i j, Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) =
      algebraMap ℚ Q (Algebra.trace ℚ L (bL i * bL j)) := fun i j => by
    rw [hB, hB, Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul']
  have hTM : Algebra.traceMatrix Q B = (algebraMap ℚ Q).mapMatrix (Algebra.traceMatrix ℚ bL) := by
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Algebra.traceForm_apply]
    exact htr i j
  have hdet : (Algebra.traceMatrix Q B).det = algebraMap ℚ Q (Algebra.discr ℚ bL) := by
    rw [hTM, ← RingHom.map_det, Algebra.discr_def]
  have hG : ∀ i j, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (B i * B j) := fun i j =>
    ⟨⟨_, hS v hv _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))⟩,
      (htr i j).symm⟩
  have hω : ∀ i, ∃ u : v.adicCompletionIntegers ℚ, algebraMap (v.adicCompletionIntegers ℚ) Q u =
      Algebra.trace Q (Q ⊗[ℚ] L) (E * B i) := fun i => ⟨⟨_, by rw [hB]; exact hE i⟩, rfl⟩
  obtain ⟨u, hu⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum (v.adicCompletionIntegers ℚ) Q (Q ⊗[ℚ] L) κ B E hG hω
  intro j
  have hrep : B.repr E j = (algebraMap ℚ Q (Algebra.discr ℚ bL))⁻¹ *
      algebraMap (v.adicCompletionIntegers ℚ) Q (u j) := by
    have h1 := congrArg (fun x => B.repr x j) hu

    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_sum, Finset.sum_apply', Module.Basis.repr_self, Finsupp.single_apply, hdet] at h1
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)] at h1
    simp only [if_true, mul_one] at h1
    have hne : algebraMap ℚ Q (Algebra.discr ℚ bL) ≠ 0 := (map_ne_zero _).2 hd
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  show B.repr E j ∈ v.adicCompletionIntegers ℚ
  rw [hrep, ← map_inv₀]
  exact mul_mem (hS v hv _ (Finset.mem_insert_self _ _)) (u j).2

end GlobalTheory.LocIntSpan
