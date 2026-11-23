module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTransABTwoZero
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fderiv_prod_coord {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℂ → ℂ) (L : ι → ℂ →L[ℝ] ℂ) (z : ι → ℂ)
    (hg : ∀ i, HasFDerivAt (g i) (L i) (z i)) :
    DifferentiableAt ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z ∧
    ∀ (j : ι) (v : ℂ), fderiv ℝ (fun w : ι → ℂ => ∏ i, g i (w i)) z (Pi.single j v) =
      L j v * ∏ i ∈ Finset.univ.erase j, g i (z i) := by
  have h1 : ∀ i ∈ (Finset.univ : Finset ι), HasFDerivAt (fun w : ι → ℂ => g i (w i))
      ((L i).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i)) z := fun i _ =>
    (hg i).comp z (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℂ) i).hasFDerivAt
  have h2 := HasFDerivAt.finsetProd h1
  refine ⟨h2.differentiableAt, fun j v => ?_⟩
  rw [h2.fderiv, ContinuousLinearMap.sum_apply, Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · simp

theorem hasFDerivAt_factor (c : ℂ) (a β : ℝ) (h : ℝ → ℂ) (h' : ℂ) (w : ℂ) (hh : HasDerivAt h h' (β * w.im)) :
    ∃ L : ℂ →L[ℝ] ℂ, HasFDerivAt (fun u : ℂ => Complex.exp (c * ((a * u.re : ℝ) : ℂ)) * h (β * u.im)) L w ∧
      L 1 = c * (a : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h (β * w.im)) ∧
      L I = (β : ℂ) * (Complex.exp (c * ((a * w.re : ℝ) : ℂ)) * h') := by
  have e1 : HasFDerivAt (fun u : ℂ => ((a * u.re : ℝ) : ℂ)) (Complex.ofRealCLM.comp (a • Complex.reCLM)) w :=
    (Complex.ofRealCLM.comp (a • Complex.reCLM)).hasFDerivAt
  have e2 := (e1.const_mul c).cexp
  have e3 : HasFDerivAt (fun u : ℂ => β * u.im) (β • Complex.imCLM) w := (β • Complex.imCLM).hasFDerivAt
  have e4 := hh.hasFDerivAt.comp w e3
  refine ⟨_, e2.mul e4, ?_, ?_⟩
  · simp; ring
  · simp; ring

theorem termQ_fderiv : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  intro F _ _ b ν hb H σ hσ q z hz τ₀
  have hne : ∀ τ : Emb F, τ b * (z τ).im ≠ 0 := fun τ =>
    mul_ne_zero ((map_ne_zero τ).2 hb) (hz τ).ne'
  choose L hL hL1 hLI using fun τ : Emb F => hasFDerivAt_factor (2 * (Real.pi : ℂ) * I) (τ ν * τ b) (τ b)
    (iteratedDeriv (q τ) (hTrans σ (τ ν))) _ (z τ) ((H (τ ν) (q τ) _ (hne τ)).1 σ hσ)
  obtain ⟨hd, hf⟩ := fderiv_prod_coord _ L z hL
  refine ⟨hd, ?_, ?_⟩
  · refine (hf τ₀ 1).trans ?_
    unfold termQ
    rw [hL1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀)]
    ring
  · refine (hf τ₀ I).trans ?_
    unfold termQ
    rw [hLI, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), mul_assoc]
    congr 2
    · simp
    · refine Finset.prod_congr rfl fun τ hτ => ?_
      simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hτ)]

end GlobalTheory.HeckeTwo
