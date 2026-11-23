module

import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.UnitNorm.UnrealifyRealify
public import Formalism.PeriodIntegrals.HaarDefs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Formalism.FormalDegreeBessel.FinalG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Formalism.QuantumDeterminants.Hpk k r + Formalism.QuantumDeterminants.Hpk k r * X = 0

section ExpD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  simp only [Complex.coe_smul]
  exact this

theorem exp_deriv (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ)) (fun i j => X i j) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X i j
  exact this

def mulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

def mulR (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)

end ExpD

section Grp

variable {k r : ℕ}

theorem Hpk_unit (k r : ℕ) : IsUnit (Hpk k r).det := by
  have h := (hpkFacts k r).2.1
  have : (Hpk k r).det * (Hpk k r).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ this

theorem UH_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) :=
  (uHGroup _ _ (Hpk_unit k r)).2.1 a ha b hb

theorem exp_mem_UH {X : Mx k r} (hX : InLieHpk k r X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  apply PI.WUN.exp_mem_UH <;> assumption

end Grp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

def InA (k r : ℕ) (X : Mx k r) : Prop :=
  (∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val → X i (eI k r a) = 0) ∧
    ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val → X i j = 0

def InLieN (k r : ℕ) (X : Mx k r) : Prop := InLieHpk k r X ∧ InA k r X

theorem InA.mul {X Y : Mx k r} (hX : InA k r X) (hY : InA k r Y) : InA k r (X * Y) := by
  apply PI.WUN.InA.mul <;> assumption

theorem InA.pow {X : Mx k r} (hX : InA k r X) : ∀ n : ℕ, InA k r (X ^ (n + 1)) := by
  intro n
  induction n with
  | zero => simpa using hX
  | succ n ih => rw [pow_succ]; exact ih.mul hX

theorem exp_entry_hasSum (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) ((NormedSpace.exp X) i j) := by
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X
  let L : Mx k r →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)
  have := L.hasSum h
  exact this

theorem exp_entry_of_InA {X : Mx k r} (i j : Fin (2 * r + k + 1)) (h : ∀ n : ℕ, (X ^ (n + 1)) i j = 0) :
    (NormedSpace.exp X) i j = if i = j then 1 else 0 := by
  have h1 := exp_entry_hasSum X i j
  have h2 : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) * (X ^ n) i j) (((Nat.factorial 0 : ℂ)⁻¹) * (X ^ 0) i j) := by
    apply hasSum_single 0
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [h m, mul_zero]
  rw [h1.unique h2]
  simp [Matrix.one_apply]

theorem exp_mem_N {X : Mx k r} (hX : InLieN k r X) : NormedSpace.exp X ∈ Nset k r := by
  refine ⟨?_, ?_, ?_⟩
  · have := exp_mem_UH hX.1 1
    simpa using this
  · intro a i hai
    exact exp_entry_of_InA i _ (fun n => (hX.2.pow n).1 a i hai)
  · intro i j h1 h2 h3
    exact exp_entry_of_InA i j (fun n => (hX.2.pow n).2 i j h1 h2 h3)

theorem InLieN.add {X Y : Mx k r} (hX : InLieN k r X) (hY : InLieN k r Y) : InLieN k r (X + Y) := by
  apply PI.WUN.InLieN.add <;> assumption

theorem InLieN.smul {X : Mx k r} (hX : InLieN k r X) (c : ℝ) : InLieN k r ((c : ℂ) • X) := by
  refine ⟨?_, ?_, ?_⟩
  · show ((c : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((c : ℂ) • X) = 0
    have h1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX.1
    have hst : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    rw [Matrix.conjTranspose_smul, hst, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h1, smul_zero]
  · intro a i hai
    rw [Matrix.smul_apply, hX.2.1 a i hai, smul_zero]
  · intro i j h1 h2 h3
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]

theorem InLieN.zero : InLieN k r (0 : Mx k r) := by
  refine ⟨?_, ?_, ?_⟩
  · show (0 : Mx k r)ᴴ * Hpk k r + Hpk k r * 0 = 0
    simp
  · intro a i _; rfl
  · intro i j _ _ _; rfl

theorem unrealify_add (x y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem continuous_of : Continuous (fun x : Mt k r => (Matrix.of x : Mx k r)) := continuous_id

def unrealL (k r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) →ₗ[ℝ] Mx k r where
  toFun := unrealify
  map_add' := unrealify_add
  map_smul' := by
    intro c x
    rw [unrealify_smul]
    exact Complex.coe_smul c _

end PI
