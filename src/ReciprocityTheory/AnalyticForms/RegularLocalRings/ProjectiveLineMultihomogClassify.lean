module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Compactification.OnePoint.Basic

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint Filter Topology

noncomputable section

theorem ptIdeal_isMaximal {n : ℕ} (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩

theorem sub_C_eval_mem_span {n : ℕ} (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    have : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g)) := by
      simp only [map_add (f := _)]; ring
    rw [this]; exact add_mem hf hg
  | mul_X f i hf =>
    have : f * X i - C (eval p (f * X i)) =
        (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ptIdeal_eq_span {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro f hf
    have h0 : eval p f = 0 := hf
    simpa [h0] using sub_C_eval_mem_span p f
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show eval p (X i - C (p i)) = 0
    simp

end

end ReciprocityTheory.AnForm.R
