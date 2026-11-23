module

public import CompanionTheory.HarishChandraModules.NonemptyRepresentations.NonemptyOfAntitone
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Linear

@[expose] public section

open Matrix

noncomputable section

namespace CompanionTheory.D.Inhab.HWRep

variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)

def one' (k : ℕ) : Fin k → Fin k → ℂ := (1 : Matrix (Fin k) (Fin k) ℂ)

def D (Y : Matrix (Fin k) (Fin k) ℂ) : Matrix R.I R.I ℂ :=
  Matrix.of fun i j => fderiv ℂ (fun B : Fin k → Fin k → ℂ => R.ρ (Matrix.of B) i j) (one' k) (fun a b => Y a b)

theorem D_add (Y Z : Matrix (Fin k) (Fin k) ℂ) : R.D (Y + Z) = R.D Y + R.D Z := by
  ext i j
  simp only [D, Matrix.of_apply, Matrix.add_apply]
  rw [← map_add (f := _)]; rfl

theorem D_smul (c : ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) : R.D (c • Y) = c • R.D Y := by
  ext i j
  simp only [D, Matrix.of_apply, Matrix.smul_apply]
  rw [← map_smul]; rfl

theorem hasDerivAt_curve (γ : ℝ → Matrix (Fin k) (Fin k) ℂ) (Y : Matrix (Fin k) (Fin k) ℂ) (h0 : γ 0 = 1)
    (hγ : ∀ a b, HasDerivAt (fun t => γ t a b) (Y a b) 0) (v : R.I → ℂ) :
    HasDerivAt (fun t => R.ρ (γ t) *ᵥ v) (R.D Y *ᵥ v) 0 := by
  have hγ' : HasDerivAt (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) (fun a b => Y a b) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hγ a b
  refine hasDerivAt_pi.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.mul_const ?_ _
  have hd := (R.diff (one' k) (by show (1 : Matrix (Fin k) (Fin k) ℂ).det ≠ 0; simp) i j).hasFDerivAt
  have e : one' k = (fun t => (fun a b => γ t a b : Fin k → Fin k → ℂ)) 0 := by
    funext a b; simp [h0, one']
  have hd' := hd.restrictScalars ℝ
  rw [e] at hd'
  have := hd'.comp_hasDerivAt (0 : ℝ) hγ'
  rw [← e] at this
  exact this

theorem curve_deriv (a b c d : Fin k) :
    HasDerivAt (fun t : ℝ => (1 + (t : ℂ) • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)
      ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d) 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const
    ((Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c d)).const_add ((1 : Matrix (Fin k) (Fin k) ℂ) c d)

theorem curve_tri {a b : Fin k} (hab : a ≤ b) (t : ℂ) :
    (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ).BlockTriangular id := by
  intro c d h
  have h' : d < c := h
  have : ¬(a = c ∧ b = d) := by rintro ⟨rfl, rfl⟩; exact absurd hab (not_le.2 h')
  simp [Matrix.one_apply, h'.ne', Matrix.single_apply, this]

theorem D_upper {a b : Fin k} (hab : a < b) : R.D (Matrix.single a b 1) *ᵥ R.v0 = 0 := by
  have h := R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) _ (by simp)
    (curve_deriv a b) R.v0
  have hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a b (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c = 1 := by
    intro t c
    have : ¬(a = c ∧ b = c) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
    simp [Matrix.single_apply, this]
  have e : (fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a b (1 : ℂ)) *ᵥ R.v0) = fun _ => R.v0 := by
    funext t
    rw [R.hw _ (curve_tri hab.le _)]
    · simp only [hdiag]; simp
    · rw [Matrix.det_of_upperTriangular (curve_tri hab.le _)]
      simp only [hdiag]; simp
  rw [e] at h
  exact h.unique (hasDerivAt_const _ _)

theorem D_diag (a : Fin k) : R.D (Matrix.single a a 1) *ᵥ R.v0 = (ν a : ℂ) • R.v0 := by
  have h := R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) _ (by simp)
    (curve_deriv a a) R.v0
  have hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a a (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c =
      if c = a then 1 + t else 1 := by
    intro t c
    by_cases hc : c = a
    · simp [hc]
    · simp [Matrix.single_apply, hc, Ne.symm hc]
  have h1 : HasDerivAt (fun t : ℝ => (1 : ℂ) + t) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add (1 : ℂ)
  have hne : ∀ᶠ t : ℝ in nhds 0, (1 : ℂ) + t ≠ 0 :=
    h1.continuousAt.eventually_ne (by simp)
  have e : (fun t : ℝ => ((1 : ℂ) + t) ^ ν a • R.v0) =ᶠ[nhds 0]
      fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) *ᵥ R.v0 := by
    filter_upwards [hne] with t ht
    rw [R.hw _ (curve_tri le_rfl _)]
    · congr 1
      simp only [hdiag]
      rw [Finset.prod_eq_single a] <;> simp +contextual
    · rw [Matrix.det_of_upperTriangular (curve_tri le_rfl _)]
      simp only [hdiag]
      exact Finset.prod_ne_zero_iff.2 fun c _ => by split_ifs <;> simp [ht]
  have hz : HasDerivAt (fun x : ℂ => x ^ ν a) (ν a : ℂ) ((1 : ℂ) + ((0 : ℝ) : ℂ)) := by
    simpa using hasDerivAt_zpow (ν a) (1 : ℂ) (Or.inl one_ne_zero)
  have h2 : HasDerivAt (fun t : ℝ => ((1 : ℂ) + t) ^ ν a) (ν a : ℂ) 0 := by
    have := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply] at this
    exact this
  exact (h.congr_of_eventuallyEq e).unique (h2.smul_const R.v0)

end CompanionTheory.D.Inhab.HWRep
