module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import GroundTheory.AutomorphicForms.CuspidalAdmissible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem prj_prj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : prj V ∘L prj V = prj V := by
  ext v
  simp only [prj, ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)

private theorem rhoL_prj {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) {k : GL (Fin n) (w.adicCompletion K)} (hk : k ∈ J) :
    rhoL μ w k ∘L prj (fixL μ w J) = prj (fixL μ w J) := by
  ext1 v
  have hle : (fixL μ w J).topologicalClosure ≤
      LinearMap.eqLocus (rhoL μ w k : LL μ →ₗ[ℂ] LL μ) LinearMap.id := by
    apply Submodule.topologicalClosure_minimal
    · unfold fixL fixF rhoL
      exact iInf₂_le (AdelicGLn.localEmbedding w k) (Subgroup.mem_map_of_mem _ hk)
    · exact isClosed_eq (rhoL μ w k).continuous continuous_id
  exact hle (Submodule.starProjection_apply_mem _ v)

private theorem hop_one {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) : Hop μ w J 1 = prj (fixL μ w J) := by
  have hs : {c : GL (Fin n) (w.adicCompletion K) ⧸ J | ∃ k ∈ J, c = QuotientGroup.mk (k * 1)} =
      {QuotientGroup.mk 1} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, mul_one]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact QuotientGroup.eq.mpr (by simpa using hk)
    · rintro rfl
      exact ⟨1, J.one_mem, rfl⟩
  unfold Hop
  rw [hs, finsum_mem_singleton]
  apply rhoL_prj
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul J (1 : GL (Fin n) (w.adicCompletion K))
  rw [hh, one_mul]
  exact h.2

theorem UpperTheory.ConvolutionTheory.C.uiwPow :
    UpperTheory.ConvolutionTheory.C.UiwPow := by
  intro K _ _ n μ _ w ν hν j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, zero_smul, Uiw, GroundTheory.Automorphic.Parabolic.diagPow_zero, hop_one]
    rfl
  · rw [(UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w ν ν hν hν).2.1 j hj, Uiw, Hop, ContinuousLinearMap.comp_assoc, prj_prj]
