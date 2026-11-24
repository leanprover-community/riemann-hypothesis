module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i))

def IsRadicalAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  ∀ f ∈ I.radical, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * f ∈ I

theorem eval_linPoly (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly L i) = (L *ᵥ x) i := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem zeroSet_sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) : zeroSet (sliceIdeal J L q) = zeroSet J ∩ {x | L *ᵥ x = L *ᵥ q} := by
  ext x
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun f hf => h f (Ideal.mem_sup_left hf), funext fun i => ?_⟩
    have := h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rwa [map_sub, eval_linPoly, eval_C, sub_eq_zero] at this
  · rintro ⟨hJ, hL⟩ f hf
    have hle : sliceIdeal J L q ≤ RingHom.ker (eval x) := by
      refine sup_le (fun g hg => RingHom.mem_ker.2 (hJ g hg)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_linPoly, eval_C, hL, sub_self]
    exact RingHom.mem_ker.1 (hle hf)

end

end GroundTheory.Heights₂.Heights
