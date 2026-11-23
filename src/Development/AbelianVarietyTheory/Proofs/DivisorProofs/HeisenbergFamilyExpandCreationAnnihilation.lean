module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem sum_unitAt {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ} (c : W → Matrix (Ix P Q) (Ix R S) ℂ) :
    c = ∑ j : W × (Ix P Q × Ix R S), unitAt j (c j.1 j.2.1 j.2.2) := by
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [← Finset.univ_sum_single c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fintype.sum_prod_type]
  conv_lhs => rw [Matrix.matrix_eq_sum_single (c w)]
  funext v
  simp only [unitAt, Finset.sum_apply]
  by_cases h : v = w
  · subst h
    simp
  · simp [h]

theorem unitAt_re_im {W : Type} [DecidableEq W] {P Q R S : ℕ} (j : W × (Ix P Q × Ix R S)) (z : ℂ) :
    unitAt j z = ((z.re : ℝ) : ℂ) • unitAt j 1 + ((z.im : ℝ) : ℂ) • unitAt j Complex.I := by
  simp only [unitAt, ← Pi.single_smul', ← Pi.single_add, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, mul_one,
    Complex.re_add_im]

theorem heis_expand : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : ℕ}
    (H : (W → Matrix (Ix P Q) (Ix R S) ℂ) → Module.End ℂ V),
    (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) →
    ∀ c : W → Matrix (Ix P Q) (Ix R S) ℂ, H c = ∑ j : W × (Ix P Q × Ix R S),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • GlobalTheory.CCRFock.fockD H j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul c
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (W → Matrix (Ix P Q) (Ix R S) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : W × (Ix P Q × Ix R S), H (unitAt j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAt c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAt_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold fockM fockD coefM coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAt j 1) = A
  generalize H (unitAt j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.CCRFock
