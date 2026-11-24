module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRealTensorToProdMatrixAlgebrasInfPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRestrictScalarsField
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AutomorphicArithmetic.RealSpanData.RealData

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private def psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) : G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ :=
  if (InfinitePlace.mk σ).embedding = σ then G.psi (InfinitePlace.mk σ)
  else ((starRingEnd ℂ).mapMatrix).comp (G.psi (InfinitePlace.mk σ))

private theorem psiE_F {p : ℕ} [Fact p.Prime] (G : HTGroup p) (σ : G.F →+* ℂ) (x : G.F) :
    psiE G σ (algebraMap G.F G.C x) = Matrix.scalar (Fin G.n) (σ x) := by
  unfold psiE
  split_ifs with h
  · rw [G.psi_F, h]
  · have h2 : (InfinitePlace.mk σ).embedding = ComplexEmbedding.conjugate σ :=
      (InfinitePlace.embedding_mk_eq σ).resolve_left h
    rw [RingHom.comp_apply, G.psi_F, h2]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, ComplexEmbedding.conjugate_coe_eq]

private theorem sum_psiE {p : ℕ} [Fact p.Prime] (G : HTGroup p) (c : G.C) :
    ∑ σ : G.F →+* ℂ, Matrix.trace (psiE G σ c) =
      ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : G.F →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hne : ComplexEmbedding.conjugate v.embedding ≠ v.embedding := fun h =>
    (InfinitePlace.isComplex_iff.1 (IsTotallyComplex.isComplex v)) h
  have hf : (Finset.univ.filter fun σ : G.F →+* ℂ => InfinitePlace.mk σ = v) =
      {v.embedding, ComplexEmbedding.conjugate v.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro rfl
      rcases InfinitePlace.embedding_mk_eq σ with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        rw [h]
        exact (star_star σ).symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding v
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [hf, Finset.sum_pair hne.symm]
  have h1 : psiE G v.embedding = G.psi v := by
    unfold psiE
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  have h2 : psiE G (ComplexEmbedding.conjugate v.embedding) = ((starRingEnd ℂ).mapMatrix).comp (G.psi v) := by
    unfold psiE
    rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg hne.symm]
  rw [h1, h2, RingHom.comp_apply]
  have h3 : Matrix.trace (((starRingEnd ℂ).mapMatrix) (G.psi v c)) = (starRingEnd ℂ) (Matrix.trace (G.psi v c)) := by

    simp [Matrix.trace, map_sum]
  rw [h3, Complex.add_conj]

private theorem trace_rep {p : ℕ} [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (c : G.C) :
    ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) =
      2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re := by
  have h3 : Module.finrank ℚ G.F = Module.finrank ℚ D.F :=
    (AlgEquiv.ofRingEquiv (f := L.e) (fun r => by simp)).toLinearEquiv.finrank_eq.symm
  have h4 : Module.finrank ℚ (VQ D) = D.m * G.n * Module.finrank ℚ G.F := by
    haveI := D.freeLa
    rw [h3, L.n_eq, ← D.rankLa]
    exact Module.finrank_baseChange
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  have hq := GlobalTheory.QTrace.q_trace (F := G.F) (A := G.C) (V := VQ D) G.n G.rankC L.rep.toRingHom (psiE G) (psiE_F G) c
  rw [sum_psiE, h4] at hq
  have hn : (G.n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 G.n_pos.ne'
  have hd : ((Module.finrank ℚ G.F : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  push_cast at hq
  have hq' : ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℂ) =
      (D.m : ℂ) * ∑ v : InfinitePlace G.F, ((2 * (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    have : (G.n : ℂ) * (Module.finrank ℚ G.F : ℂ) ≠ 0 := mul_ne_zero hn hd
    apply mul_left_cancel₀ this
    push_cast
    linear_combination hq
  have : (((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) : ℂ) =
      ((2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psi v c)).re : ℝ) : ℂ) := by
    push_cast at hq' ⊢
    rw [hq', Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  exact_mod_cast this

theorem UpperTheory.trace_action_eq_sum_places :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (x : ℝ ⊗[ℚ] G.C), LinearMap.trace ℝ (ℝ ⊗[ℚ] VQ D) (actOn L.rep ℝ x) = 2 * (D.m : ℝ) * ∑ v : InfinitePlace G.F, (Matrix.trace (G.psiR v x)).re := by
  intro p _ D G L x
  haveI : FiniteDimensional ℚ (VQ D) := by
    haveI := D.finLa
    infer_instance
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add (f := _), Matrix.trace_add, Complex.add_re, Finset.sum_add_distrib, hx, hy, mul_add]
  | tmul r c =>
    have h1 : actOn L.rep ℝ (r ⊗ₜ[ℚ] c) = r • (L.rep c).baseChange ℝ := by
      rw [Algebra.smul_def]
      exact Algebra.TensorProduct.lift_tmul _ _ _ r c
    rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul]
    have h2 : (algebraMap ℚ ℝ) (LinearMap.trace ℚ (VQ D) (L.rep c)) = ((LinearMap.trace ℚ (VQ D) (L.rep c) : ℚ) : ℝ) := rfl
    rw [h2, trace_rep]
    simp only [HTGroup.psiR_tmul, Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, ← Finset.mul_sum]
    ring
