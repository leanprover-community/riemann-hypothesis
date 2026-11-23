module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebClosed
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.TwoNode
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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

open MvPolynomial Filter Topology

private noncomputable def UpperTheory.ConvolutionTheory.FX.sepNode (y : ℝ) (b : Bool) : ℝ :=
  if b then y + Real.sqrt (y ^ 2 - 1) else y - Real.sqrt (y ^ 2 - 1)

private theorem UpperTheory.ConvolutionTheory.FX.sepNode_quad (y : ℝ) (hy : 1 < y) (b : Bool) :
    UpperTheory.ConvolutionTheory.FX.sepNode y b ^ 2 + 1 = 2 * y * UpperTheory.ConvolutionTheory.FX.sepNode y b := by
  have hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  cases b <;> simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] <;>
    linear_combination hs

private theorem UpperTheory.ConvolutionTheory.FX.sepNode_inj (y y' : ℝ) (hy : 1 < y) (hy' : 1 < y') (b b' : Bool)
    (h : UpperTheory.ConvolutionTheory.FX.sepNode y b = UpperTheory.ConvolutionTheory.FX.sepNode y' b') : y = y' ∧ b = b' := by
  have q := UpperTheory.ConvolutionTheory.FX.sepNode_quad y hy b
  have q' := UpperTheory.ConvolutionTheory.FX.sepNode_quad y' hy' b'
  rw [← h] at q'
  have ht : UpperTheory.ConvolutionTheory.FX.sepNode y b ≠ 0 := by
    intro h0
    rw [h0] at q
    norm_num at q
  have hyy : y = y' := by
    apply mul_right_cancel₀ ht
    linarith
  subst hyy
  refine ⟨rfl, ?_⟩
  have hs : 0 < Real.sqrt (y ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  cases b <;> cases b' <;>
    simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] at h <;>
    first | rfl | (exfalso; linarith)

theorem UpperTheory.ConvolutionTheory.FX.separate0 :
    ∀ (η : ℝ), 0 < η → ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (m j : ℕ) (c : I → ℂ) (ε : ℝ),
    (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * (((Polynomial.Chebyshev.T ℝ ((m + s : ℕ) : ℤ)).eval (2 * a i / η - 1) : ℝ) : ℂ) * ζ i ^ (j + s')‖ ≤ ε) →
    ∀ i, ‖c i‖ * (2 * a i / η - 1) ^ m * ‖ζ i‖ ^ j ≤ K * ε := by
  intro η hη I _ a ζ ha _ hinj
  have hy : ∀ i, 1 < 2 * a i / η - 1 := fun i => by
    have : 2 < 2 * a i / η := by
      rw [lt_div_iff₀ hη]
      linarith [ha i]
    linarith
  obtain ⟨s₀, K, hK⟩ := UpperTheory.ConvolutionTheory.FX.two_node (I × Bool)
    (fun p => ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ)) (fun p => ζ p.1) (by
      rintro ⟨i, b⟩ ⟨i', b'⟩ h
      simp only [Prod.mk.injEq, Complex.ofReal_inj] at h
      obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.FX.sepNode_inj _ _ (hy i) (hy i') _ _ h.1
      have h3 : a i = a i' := by
        field_simp at h1
        linarith
      have h4 : i = i' := hinj (Prod.ext h3 h.2)
      rw [h4, h2])
  refine ⟨s₀, 2 * K, fun m j c ε hε i => ?_⟩
  have key := hK (fun p => c p.1 *
      ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ) ^ m * ζ p.1 ^ j / 2) ε (by
    intro s hs s' hs'
    refine le_of_eq_of_le ?_ (hε s hs s' hs')
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((UpperTheory.ConvolutionTheory.FX.cheb_facts (m + s) _).2 (hy i).le).1, Fintype.sum_bool]
    simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false]
    generalize Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r
    generalize 2 * a i / η - 1 = y
    push_cast
    ring) (i, true)
  simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true] at key
  have hyi := hy i
  have hr := Real.sqrt_nonneg ((2 * a i / η - 1) ^ 2 - 1)
  generalize Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r at key hr
  generalize 2 * a i / η - 1 = y at key hyi
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ y + r), Complex.norm_two] at key
  have h5 : ‖c i‖ * y ^ m * ‖ζ i‖ ^ j ≤ ‖c i‖ * (y + r) ^ m * ‖ζ i‖ ^ j := by
    have : y ≤ y + r := by linarith
    have : 0 ≤ y := by linarith
    gcongr
  linarith
