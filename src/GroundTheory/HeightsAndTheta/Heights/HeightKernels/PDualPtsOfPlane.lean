module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualProjApply
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

namespace DualPointsOfPlane

theorem map_eval₂_int {ι A B : Type*} [CommRing A] [CommRing B] (k : A →+* B) (c : ℤ →+* A) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (eval₂ c g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _

theorem map_aeval_int {ι A B : Type*} [CommRing A] {_ : Algebra ℤ A} [CommRing B] (k : A →+* B) (g : ι → A)
    (f : MvPolynomial ι ℤ) :
    k (aeval g f) = eval₂ (Int.castRingHom B) (k ∘ g) f := by
  rw [aeval_def, map_eval₂_int]

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

def formPoly (b : Module.Basis T ℤ (dualLattice F)) (p : Σ _ : Unit, T) : MvPolynomial (Fin i) K :=
  ∑ j, C ((b p.2 : Fin i → K) j) * X j


omit [Fintype T] [DecidableEq T] in
theorem dualPlanePt_eq_mulVec [DecidableEq (K →+* ℂ)] (b : Module.Basis T ℤ (dualLattice F))
    (σ : K →+* ℂ) (v : Fin i → ℂ) (t : T) :
    dualPlanePt b σ v ⟨(), t⟩ =
      (dualEmbMatrix b *ᵥ fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) t := by
  simp only [dualPlanePt, mulVec, dotProduct, dualEmbMatrix, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single σ]
  · simp
  · intro τ hτ
    simp [hτ]


omit [Fintype T] [DecidableEq T] in
theorem eval₂_formPoly (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) (v : Fin i → ℂ)
    (p : Σ _ : Unit, T) :
    eval₂Hom σ v (formPoly b p) = dualPlanePt b σ v p := by
  simp [formPoly, dualPlanePt]

end DualPointsOfPlane


open DualPointsOfPlane in
theorem DualPtsOfPlane.proof : DualPtsOfPlane.Statement := by
  intro K _ _ i F T _ _ b hb σ v hv
  classical
  refine ⟨fun _ => ?_, fun f hf => ?_⟩
  · have hw : (fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) ≠ 0 := by
      intro h0
      apply hv
      funext j
      simpa using congrFun h0 (σ, j)
    have hne : dualEmbMatrix b *ᵥ (fun p : (K →+* ℂ) × Fin i => if p.1 = σ then v p.2 else 0) ≠ 0 := by
      intro h0
      apply hw
      apply hb.1
      rw [map_zero, Matrix.mulVecLin_apply]
      exact h0
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hne
    exact ⟨t, by rw [dualPlanePt_eq_mulVec]; exact ht⟩
  · have h0 : mConeMap (dualLatticeCoord b) f = 0 := hf
    have h1 := congrArg (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) h0
    unfold mConeMap at h1
    rw [map_zero, map_aeval_int] at h1
    have hy : (MvPolynomial.eval fun _ : Unit => (1 : ProjField K i)) ∘
        (fun p => C (dualLatticeCoord b p) * X p.1) =
        (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)) ∘ formPoly b := by
      funext p
      simp [dualLatticeCoord, formPoly]
    rw [hy, ← map_eval₂_int (c := Int.castRingHom _)] at h1
    have h2 : eval₂ (Int.castRingHom _) (formPoly b) f = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h1
    have h3 := congrArg (eval₂Hom σ v) h2
    rw [map_zero, map_eval₂_int] at h3
    have hz : (eval₂Hom σ v) ∘ formPoly b = dualPlanePt b σ v := funext (eval₂_formPoly b σ v)
    rw [hz] at h3
    rw [eval_map]
    exact h3

end

end GroundTheory.Heights₂.Heights
