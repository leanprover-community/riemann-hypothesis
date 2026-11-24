module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ContinuousLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.WeilBound.ThetaLifts.TowerModels.LeviAd

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Distribution.SchwartzSpace.Basic\npublic import Mathlib.MeasureTheory.Measure.Haar.OfBasis\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\npublic import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier\nimport Mathlib.Analysis.LocallyConvex.AbsConvexOpen\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.LinearAlgebra.Matrix.FiniteDimensional\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Analysis.Complex.Circle\n\n"}
section -- clump:auto
@[expose] public section

namespace UpperTheory.Reformulated.B.P6.r12b
open FourierTransform MeasureTheory Complex Real Module

theorem integral_comp_linearEquiv_eq_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (e : V ≃L[ℝ] E) :
    ∃ c : NNReal, ∀ F : E → ℂ, ∫ v, F (e v) ∂μ = c • ∫ w, F w := by
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ.map e = c • (volume : Measure E) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  refine ⟨c, fun F => ?_⟩
  have h1 : ∫ v, F (e v) ∂μ = ∫ w, F w ∂(μ.map e) := by
    have := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv F
    simpa using this.symm
  rw [h1, hc, integral_smul_nnreal_measure]

theorem exists_equiv_inner_of_nondegenerate {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0) (e : V ≃L[ℝ] E) :
    ∃ A : V ≃L[ℝ] E, ∀ u v, B u v = inner ℝ (A u) (e v) := by
  let L : V →ₗ[ℝ] E →ₗ[ℝ] ℝ := B.compl₂ (e.symm : E →ₗ[ℝ] V)
  let Φ : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := innerₗ E
  have hΦ : ∀ x y, Φ x y = inner ℝ x y := fun x y => by simp [Φ]
  have hΦi : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : inner ℝ x x = (0 : ℝ) := by rw [← hΦ, hx]; rfl
    exact inner_self_eq_zero.mp h0
  have hdim : finrank ℝ E = finrank ℝ (E →ₗ[ℝ] ℝ) := (Subspace.dual_finrank_eq).symm
  have hΦs : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦi
  let Φe : E ≃ₗ[ℝ] (E →ₗ[ℝ] ℝ) := LinearEquiv.ofBijective Φ ⟨hΦi, hΦs⟩
  have hΦe : ∀ x, Φe x = Φ x := fun x => rfl
  let a : V →ₗ[ℝ] E := Φe.symm.toLinearMap ∘ₗ L
  have ha : ∀ u w, inner ℝ (a u) w = B u (e.symm w) := by
    intro u w
    rw [← hΦ, ← hΦe]
    simp [a, L]
  have hai : Function.Injective a := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply hB u
    intro v
    have := ha u (e v)
    rw [hu, inner_zero_left, e.symm_apply_apply] at this
    exact this.symm
  have hdim2 : finrank ℝ V = finrank ℝ E := e.toLinearEquiv.finrank_eq
  have has : Function.Surjective a :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim2).mp hai
  let A : V ≃L[ℝ] E := (LinearEquiv.ofBijective a ⟨hai, has⟩).toContinuousLinearEquiv
  refine ⟨A, fun u v => ?_⟩
  have hA : A u = a u := rfl
  rw [hA, ha, e.symm_apply_apply]

theorem GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_bilinear_transform.{u_1} :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V] [inst_1 : NormedSpace ℝ V] [FiniteDimensional ℝ V] [inst_3 : MeasurableSpace V] [BorelSpace V] (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ (u : V), (∀ (v : V), DFunLike.coe (DFunLike.coe B u) v = OfNat.ofNat (nat_lit 0)) → u = OfNat.ofNat (nat_lit 0)) → ∀ (φ : SchwartzMap V ℂ), ∃ (ψ : SchwartzMap V ℂ), DFunLike.coe ψ = fun (u : V) ↦ ∫ (v : V), Complex.exp (OfNat.ofNat (nat_lit 2) * Complex.ofReal Real.pi * Complex.I * Complex.ofReal (DFunLike.coe (DFunLike.coe B u) v)) * DFunLike.coe φ v ∂μ := by
  intro V _ _ _ _ _ μ _ B hB φ
  let E := EuclideanSpace ℝ (Fin (finrank ℝ V))
  let e : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E])
  obtain ⟨A, hA⟩ := exists_equiv_inner_of_nondegenerate B hB e
  obtain ⟨c, hc⟩ := integral_comp_linearEquiv_eq_smul μ e
  let g : SchwartzMap E ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm φ
  have hg : ∀ w, g w = φ (e.symm w) := fun w => rfl
  let N : V ≃L[ℝ] E := A.trans (ContinuousLinearEquiv.neg ℝ)
  let h : SchwartzMap V ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ N (𝓕 g)
  have hh : ∀ u, h u = (𝓕 g) (-(A u)) := fun u => rfl
  refine ⟨((c : ℝ) : ℂ) • h, ?_⟩
  funext u
  have hF : ∀ w : E, (𝓕 g) w = ∫ x, Complex.exp (-(2 * π * I * (inner ℝ x w : ℝ))) * g x := by
    intro w
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    congr 1; ext x
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 1; push_cast; ring_nf
  let F : E → ℂ := fun w => Complex.exp (2 * π * I * (inner ℝ (A u) w : ℝ)) * φ (e.symm w)
  have hint : (fun v => Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v) = fun v => F (e v) := by
    funext v
    simp only [F, hA, e.symm_apply_apply]
  have hL : (((c : ℝ) : ℂ) • h) u = ((c : ℝ) : ℂ) * ∫ w, F w := by
    rw [SchwartzMap.smul_apply, hh, hF, smul_eq_mul]
    congr 1
    congr 1; ext x
    rw [hg, inner_neg_right, real_inner_comm]
    congr 2
    push_cast; ring
  rw [hL]
  show _ = ∫ v, Complex.exp (2 * π * I * ((B u v : ℝ) : ℂ)) * φ v ∂μ
  rw [hint, hc F, NNReal.smul_def, Complex.real_smul]

end UpperTheory.Reformulated.B.P6.r12b
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix", "h": "module\n\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Distribution.SchwartzSpace.Basic\npublic import Mathlib.LinearAlgebra.Complex.FiniteDimensional\npublic import Mathlib.MeasureTheory.Measure.Haar.OfBasis\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped Matrix SchwartzMap FourierTransform RealInnerProductSpace
open MeasureTheory

namespace GlobalTheory.CompanionTheory.FourierMatrix

theorem trace_conjTranspose_mul (m n : ℕ) (u v : Fin m → Fin n → ℂ) :
    Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) = ∑ j, ∑ i, star (u i j) * v i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

noncomputable def traceForm (m n : ℕ) (s : ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re)
    (by
      intro a b c
      simp only [trace_conjTranspose_mul, Pi.add_apply, star_add, add_mul,
        Finset.sum_add_distrib, mul_add, Complex.add_re])
    (by
      intro r a b
      have : ∑ j, ∑ i, star ((r • a) i j) * b i j
          = (r : ℂ) * ∑ j, ∑ i, star (a i j) * b i j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.real_smul, mul_assoc]
      rw [trace_conjTranspose_mul, trace_conjTranspose_mul, this, mul_left_comm,
        Complex.re_ofReal_mul, smul_eq_mul])
    (by
      intro a b c
      simp only [trace_conjTranspose_mul, Pi.add_apply, mul_add,
        Finset.sum_add_distrib, Complex.add_re])
    (by
      intro r a b
      have : ∑ j, ∑ i, star (a i j) * (r • b) i j
          = (r : ℂ) * ∑ j, ∑ i, star (a i j) * b i j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, Complex.real_smul]
        ring
      rw [trace_conjTranspose_mul, trace_conjTranspose_mul, this, mul_left_comm,
        Complex.re_ofReal_mul, smul_eq_mul])

theorem traceForm_apply (m n : ℕ) (s : ℂ) (u v : Fin m → Fin n → ℂ) :
    traceForm m n s u v = (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re := rfl

theorem traceForm_nondegenerate (m n : ℕ) (s : ℂ) (hs : s ≠ 0) (u : Fin m → Fin n → ℂ)
    (h : ∀ v, traceForm m n s u v = 0) : u = 0 := by
  have h0 := h (fun i j => star s * u i j)
  rw [traceForm_apply, trace_conjTranspose_mul] at h0
  have h1 : s * ∑ j, ∑ i, star (u i j) * (star s * u i j)
      = ((Complex.normSq s * ∑ j, ∑ i, Complex.normSq (u i j) : ℝ) : ℂ) := by
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h1, Complex.ofReal_re] at h0
  have hsn : Complex.normSq s ≠ 0 := by simpa [Complex.normSq_eq_zero] using hs
  have h2 : ∑ j, ∑ i, Complex.normSq (u i j) = 0 := by
    rcases mul_eq_zero.mp h0 with h3 | h3
    · exact absurd h3 hsn
    · exact h3
  funext i j
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i j))).mp h2 j
    (Finset.mem_univ j)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (u i j))).mp h3 i (Finset.mem_univ i)
  simpa [Complex.normSq_eq_zero] using h4

theorem exists_schwartz_trace_transform :
    ∀ (m n : ℕ) (C s : ℂ), s ≠ 0 → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => C * ∫ v : Fin m → Fin n → ℂ,
        Complex.exp (2 * Real.pi * Complex.I *
          ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * φ v := by
  intro m n C s hs φ
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin m → Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨ψ, hψ⟩ := _root_.UpperTheory.Reformulated.B.P6.r12b.GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_bilinear_transform (volume : Measure (Fin m → Fin n → ℂ))
    (traceForm m n s) (traceForm_nondegenerate m n s hs) φ
  refine ⟨C • ψ, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, hψ, smul_eq_mul, traceForm_apply]

end GlobalTheory.CompanionTheory.FourierMatrix
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Mathlib.Analysis.Distribution.SchwartzSpace.Basic\npublic import Mathlib.LinearAlgebra.Complex.FiniteDimensional\npublic import Mathlib.MeasureTheory.Measure.Haar.OfBasis\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFourierTransformMatrix\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.CompFinFinOne\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ContinuousLoc\nimport Development.WeilBound.ThetaLifts.TowerModels.LeviAd\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def insW (d : SD σ) (w : InfinitePlace F) (z : ℂ) : AE F E := (Place.exists_sec d.cm d.B.emb).choose (Pi.single w z)

section

variable (d : SD σ) (w : InfinitePlace F)

theorem insW_self (z : ℂ) : piInf (d.B.emb w) (insW d w z) = z := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, h.2.1, Pi.single_eq_same]

theorem insW_ne {w' : InfinitePlace F} (hw : w' ≠ w) (z : ℂ) : piInf (d.B.emb w') (insW d w z) = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, h.2.1, Pi.single_eq_of_ne hw]

theorem insW_fin (z : ℂ) : finOne F • insW d w z = 0 := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, h.2.2.1]

theorem insW_add (z z' : ℂ) : insW d w (z + z') = insW d w z + insW d w z' := by
  have h := (Place.exists_sec d.cm d.B.emb).choose_spec
  rw [insW, insW, insW, Pi.single_add, h.2.2.2.1]

end

def insL {d : SD σ} (R : RD d) (w : InfinitePlace F) (v : Fin d.m → Fin d.n → ℂ) : Mx F E d.m d.n :=
  ((R.fr w).1 * (Matrix.of v).map star).map (insW d w)

section

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

def Supp (Z : Mx F E d.m d.n) : Prop := (∀ w', w' ≠ w → d.cw w' Z = 0) ∧ finOne F • Z = 0

theorem cw_insL (v : Fin d.m → Fin d.n → ℂ) : d.cw w (insL R w v) = (R.fr w).1 * (Matrix.of v).map star := by
  ext i j
  simp only [SD.cw, insL, Matrix.map_apply, insW_self]

theorem insL_supp (v : Fin d.m → Fin d.n → ℂ) : Supp w (insL R w v) := by
  refine ⟨fun w' hw' => ?_, ?_⟩
  · ext i j
    simp only [SD.cw, insL, Matrix.map_apply, insW_ne d w hw', Matrix.zero_apply]
  · ext i j
    simp only [insL, Matrix.smul_apply, Matrix.map_apply, insW_fin, Matrix.zero_apply]

theorem insL_add (v v' : Fin d.m → Fin d.n → ℂ) : insL R w (v + v') = insL R w v + insL R w v' := by
  have e : (R.fr w).1 * (Matrix.of (v + v')).map star =
      (R.fr w).1 * (Matrix.of v).map star + (R.fr w).1 * (Matrix.of v').map star := by
    rw [← Matrix.mul_add]
    congr 1
    ext i j
    simp
  unfold insL
  rw [e]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, insW_add]

theorem insL_zero : insL R w 0 = 0 := by
  have h := insL_add R w 0 0
  rw [add_zero] at h
  calc insL R w 0 = insL R w 0 + insL R w 0 - insL R w 0 := by abel
    _ = insL R w 0 - insL R w 0 := by rw [← h]
    _ = 0 := sub_self _

theorem insL_loc {Z : Mx F E d.m d.n} (hZ : Supp w Z) : insL R w (R.loc w Z) = Z := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · by_cases hw : w' = w
    · rw [hw]
      change d.cw w (insL R w (R.loc w Z)) = d.cw w Z
      rw [cw_insL]
      have h2 : (Matrix.of (R.loc w Z)).map star = ((R.fr w)⁻¹).1 * d.cw w Z := by
        ext i j
        exact star_star _
      rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    · change d.cw w' (insL R w (R.loc w Z)) = d.cw w' Z
      rw [(insL_supp R w _).1 w' hw, hZ.1 w' hw]
  · rw [(insL_supp R w _).2, hZ.2]

theorem rest_inv (X Z : Mx F E d.m d.n) (hZ : Supp w Z) :
    (X + Z) - insL R w (R.loc w (X + Z)) = X - insL R w (R.loc w X) := by
  rw [KFock.loc_add' d R w X Z, insL_add, insL_loc R w hZ]
  abel

end

section

variable (d : SD σ)

theorem psi_add_right (ε : ℤˣ) (X Z Z' : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (Z + Z'))) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z')) := by
  have e : d.gram X (Z + Z') = d.gram X Z + d.gram X Z' := by
    unfold SD.gram
    rw [Matrix.map_add _ (map_add _), Matrix.mul_add]
  rw [e, SD.tt, SD.tt, SD.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]

theorem psi_add_left (ε : ℤˣ) (X X' Z : Mx F E d.m d.n) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (X + X') Z)) =
      d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X Z)) * d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X' Z)) := by
  have e : d.gram (X + X') Z = d.gram X Z + d.gram X' Z := by
    unfold SD.gram
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul]
  rw [e, SD.tt, SD.tt, SD.tt, Matrix.trace_add, map_add (f := _), mul_add, AddChar.map_add_eq_mul]

theorem cw_gram (w : InfinitePlace F) (X Z : Mx F E d.m d.n) :
    d.cw w (d.gram X Z) = (d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * (d.cw w Z).map star := by
  unfold SD.gram SD.cw
  have hJ : (incM F d.A.J).map (piInf (d.B.emb w)) = d.A.J.map (d.B.emb w).1 := by
    ext i j
    simp [incM, PositivityTheory.ThKG.Tow.Levi.piInf_incl]
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Place.map_cA d.cm (d.B.emb w) Z, hJ]

theorem gram_supp_cmp (w : InfinitePlace F) {Z' Z : Mx F E d.m d.n} (hZ' : Supp w Z') (hZ : d.cw w Z = 0) :
    d.gram Z' Z = 0 := by
  refine Place.mat_ext d.cm d.B.emb (fun w' => ?_) ?_
  · change d.cw w' (d.gram Z' Z) = d.cw w' 0
    rw [cw_gram]
    by_cases hw : w' = w
    · subst hw
      rw [hZ, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
      ext i j
      simp [SD.cw]
    · rw [hZ'.1 w' hw, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
      ext i j
      simp [SD.cw]
  · unfold SD.gram
    rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, hZ'.2]
    simp

theorem psi_zero_gram (ε : ℤˣ) : d.B.ψ (((ε : ℤ) : AF F) * d.tt (0 : Mx F E d.n d.n)) = 1 := by
  simp [SD.tt]

end

theorem zeta_ne {d : SD σ} (R : RD d) : R.ζ ≠ 0 := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp

section

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem cw_loc (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have h2 : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [h2, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]

theorem frJ : (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by
  have h := R.hfr w
  calc (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star
      = R.ζ⁻¹ • (R.ζ • ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star)) := by
        rw [smul_smul, inv_mul_cancel₀ (zeta_ne R), one_smul]
    _ = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • 1 := by rw [h, smul_smul]

end

theorem psi_at_w (d : SD σ) (w : InfinitePlace F) (ε : ℤˣ) (M : Mx F E d.n d.n)
    (hM1 : ∀ w', w' ≠ w → d.cw w' M = 0) (hM2 : finOne F • M = 0) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt M) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((2 * (((ε : ℤ) : ℂ) * (d.cw w M).trace).re : ℝ) : ℂ)) := by
  have hz : ((ε : ℤ) : AF F) * d.tt M = Algebra.trace (AF F) (AE F E) ((ε : ℤ) • M.trace) := by
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  have ptr : ∀ u, piInf (d.B.emb u) M.trace = (d.cw u M).trace := fun u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, SD.cw, map_sum]
  rw [hz, Place.psi_trace_at d.std d.cm d.B.emb w _ ?_ ?_, map_zsmul, ptr, zsmul_eq_mul]
  · rw [smul_comm, ← Matrix.trace_smul, hM2, Matrix.trace_zero, smul_zero]
  · intro u hu
    rw [map_zsmul, ptr, hM1 u hu, Matrix.trace_zero, smul_zero]

theorem kernel {d : SD σ} (R : RD d) (w : InfinitePlace F) (ε : ℤˣ) (X : Mx F E d.m d.n) (u : Fin d.m → Fin d.n → ℂ) :
    d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram X (insL R w u))) =
      Complex.exp (2 * Real.pi * Complex.I * (((-2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u)).re : ℂ)) := by
  have hM1 : ∀ w', w' ≠ w → d.cw w' (d.gram X (insL R w u)) = 0 := by
    intro w' hw
    rw [cw_gram, (insL_supp R w u).1 w' hw, Matrix.map_zero _ (star_zero _), Matrix.mul_zero]
  have hM2 : finOne F • d.gram X (insL R w u) = 0 := by
    unfold SD.gram
    rw [← Matrix.mul_smul]
    have : finOne F • (insL R w u).map (cA σ) = (finOne F • insL R w u).map (cA σ) := by
      ext i j
      simp [map_smul]
    rw [this, (insL_supp R w u).2]
    simp
  have e1 : d.cw w (d.gram X (insL R w u)) =
      (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) := by
    rw [cw_gram, cw_loc R w X, cw_insL, Matrix.transpose_mul]
    have h3 : ((R.fr w).1 * (Matrix.of u).map star).map star = (R.fr w).1.map star * Matrix.of u := by
      ext i j
      simp [Matrix.mul_apply]
    have h4 : ((Matrix.of (R.loc w X)).map star)ᵀ = (Matrix.of (R.loc w X))ᴴ := rfl
    rw [h3, h4]
    calc (Matrix.of (R.loc w X))ᴴ * (R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * ((R.fr w).1.map star * Matrix.of u)
        = (Matrix.of (R.loc w X))ᴴ * ((R.fr w).1ᵀ * d.A.J.map (d.B.emb w).1 * (R.fr w).1.map star) * Matrix.of u := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [frJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [psi_at_w d w ε _ hM1 hM2, e1, Matrix.trace_smul, smul_eq_mul]
  congr 1
  have e2 : -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ * Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u) =
      ((-2 : ℝ) : ℂ) * (((ε : ℤ) : ℂ) * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace ((Matrix.of (R.loc w X))ᴴ * Matrix.of u))) := by
    push_cast
    ring
  rw [e2, Complex.re_ofReal_mul]
  push_cast
  ring

theorem locFT_sw {m n : ℕ} (C s : ℂ) (hs : s ≠ 0) (f : (Fin m → Fin n → ℂ) → ℂ) (hf : IsSw f) :
    IsSw (fun u => C * ∫ v : Fin m → Fin n → ℂ,
      Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * f v) := by
  obtain ⟨φ, rfl⟩ := hf
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_trace_transform m n C s hs φ
  exact ⟨ψ, hψ⟩

end PositivityTheory.SiegelWeilFormula.KW

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.PsiZeroGram =====
