module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.TwistedTraces.NormSkewAdjointLeOfEigenvalueBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
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
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.norm_generator_le_of_polynomial_annihilated :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (u : ℝ → Module.End ℂ E) (D : Module.End ℂ E) (p : ℝ → ℂ[X]) (M : ℝ), u 0 = 1 → (∀ s t, u (s + t) = u s * u t) → (∀ t x, ‖u t x‖ = ‖x‖) → (∀ x, HasDerivAt (fun t : ℝ => u t x) (D x) 0) → (∀ t, aeval (u t) (p t) = 0) → (∀ z : ℂ, (∀ t : ℝ, (p t).IsRoot (Complex.exp (z * t))) → ‖z‖ ≤ M) → ∀ x, ‖D x‖ ≤ M * ‖x‖ := by
  intro E _ _ _ u D p M h0 hadd hiso hder hroot hM x
  have hshift : ∀ (t : ℝ) (w : E), HasDerivAt (fun s : ℝ => u s w) (u t (D w)) t := by
    intro t w
    let L : E →L[ℂ] E := LinearMap.toContinuousLinearMap (u t)
    let LR : E →L[ℝ] E := L.restrictScalars ℝ
    have h1 : HasDerivAt (fun s : ℝ => LR (u s w)) (LR (D w)) 0 :=
      LR.hasFDerivAt.comp_hasDerivAt 0 (hder w)
    have h2 : HasDerivAt (fun s : ℝ => LR (u (s - t) w)) (LR (D w)) t := by
      apply HasDerivAt.comp_sub_const t t (f := fun s : ℝ => LR (u s w))
      simpa using h1
    have h3 : (fun s : ℝ => LR (u (s - t) w)) = fun s => u s w := by
      funext s
      show u t (u (s - t) w) = u s w
      rw [← Module.End.mul_apply, ← hadd]
      congr 2
      ring
    rw [h3] at h2
    exact h2
  have hinner : ∀ (t : ℝ) (a b : E), inner ℂ (u t a) (u t b) = inner ℂ a b := by
    intro t a b
    exact LinearIsometry.inner_map_map (⟨u t, hiso t⟩ : E →ₗᵢ[ℂ] E) a b
  have h0' : ∀ a : E, u 0 a = a := by
    intro a
    rw [h0]
    rfl
  have hskew : ∀ a b : E, inner ℂ (D a) b + inner ℂ a (D b) = 0 := by
    intro a b
    have h1 := (hder a).inner ℂ (hder b)
    have h2 : (fun t : ℝ => inner ℂ (u t a) (u t b)) = fun _ => inner ℂ a b := by
      funext t
      exact hinner t a b
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (inner ℂ a b))
    rw [h0', h0'] at h3
    rw [add_comm]
    exact h3
  have hev : ∀ z : ℂ, D.HasEigenvalue z → ‖z‖ ≤ M := by
    intro z hz
    obtain ⟨w, hw⟩ := hz.exists_hasEigenvector
    have hDw : D w = z • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    have hconst : ∀ t : ℝ, Complex.exp (-(z * t)) • u t w = w := by
      have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)) • u s w) 0 t := by
        intro t
        have he : HasDerivAt (fun s : ℝ => Complex.exp (-(z * s)))
            (Complex.exp (-(z * t)) * (-z)) t := by
          have hl : HasDerivAt (fun s : ℝ => -(z * (s : ℂ))) (-z) t := by
            have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
              simpa using (hasDerivAt_id t).ofReal_comp
            have h2 := h.const_mul (-z)
            simpa [neg_mul] using h2
          exact hl.cexp
        have h1 := he.smul (hshift t w)
        have h2 : Complex.exp (-(z * t)) • u t (D w) + (Complex.exp (-(z * t)) * (-z)) • u t w = 0 := by
          rw [hDw, map_smul, smul_smul, ← add_smul]
          have : Complex.exp (-(z * t)) * z + Complex.exp (-(z * t)) * (-z) = 0 := by ring
          rw [this, zero_smul]
        rw [h2] at h1
        exact h1
      intro t
      have hc := is_const_of_deriv_eq_zero (f := fun s : ℝ => Complex.exp (-(z * s)) • u s w)
        (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
      simpa [h0'] using hc
    have hut : ∀ t : ℝ, u t w = Complex.exp (z * t) • w := by
      intro t
      have h1 := congrArg (fun v => Complex.exp (z * t) • v) (hconst t)
      simp only [smul_smul] at h1
      rw [← Complex.exp_add] at h1
      simpa using h1
    apply hM
    intro t
    have hvec : (u t).HasEigenvector (Complex.exp (z * t)) w :=
      ⟨Module.End.mem_eigenspace_iff.2 (hut t), hw0⟩
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := p t) hvec
    rw [hroot t] at h1
    have h2 : (p t).eval (Complex.exp (z * t)) • w = 0 := by
      rw [← h1]
      rfl
    exact (smul_eq_zero.1 h2).resolve_right hw0
  exact UpperTheory.norm_skewAdjoint_le_of_eigenvalue_bound E D M hskew hev x
