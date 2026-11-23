module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockHarmonicRepresentative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem pcTrace_eq_zero {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem span_harm2_sup_coinv_eq_univ : ∀ (P Q R S : ℕ) (x : ℂ),
    Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  intro P Q R S x
  refine eq_top_iff.2 fun f _ => ?_
  have hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0 := by
    intro Z hZ g
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨Z, g, ?_⟩
    rw [pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]
  obtain ⟨h, hh, he⟩ := GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f
  have hd : f - h ∈ coinv P Q R S x := by
    rw [← Submodule.Quotient.eq]; exact he.symm
  have : f = h + (f - h) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span hh) hd

end GlobalTheory.HoweR
