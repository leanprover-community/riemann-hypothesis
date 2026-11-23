module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerLinear

theorem kerLin_of_kerBasic : KerBasic → KerLin := by
  intro hb X ι _ φ c hφ
  constructor
  · refine ⟨continuous_finsetSum _ fun i _ => (hφ i).1.mul continuous_const, ?_⟩
    have key : ∀ s : Finset ι, HasCompactSupport (fun y => ∑ i ∈ s, φ i y * c i) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : X.G → ℂ))
      | cons a s ha ih =>
        have h1 : HasCompactSupport (fun y => φ a y * c a) :=
          (hφ a).2.mul_right
        have h2 := h1.add ih
        have h3 : (fun y => ∑ i ∈ Finset.cons a s ha, φ i y * c i) =
            (fun y => φ a y * c a) + fun y => ∑ i ∈ s, φ i y * c i := by
          funext y
          simp [Finset.sum_cons]
        rw [h3]
        exact h2
    exact key Finset.univ
  · intro x y
    have hfin : ∀ i, (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y)).Finite :=
      fun i => (hb X (φ i) (hφ i)).1 x y
    have hfin' : ∀ i ∈ (Finset.univ : Finset ι),
        (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y) * c i).Finite := fun i _ =>
      (hfin i).subset (Function.support_mul_subset_left _ _)
    unfold ker
    rw [finsum_sum_comm _ _ hfin']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_mul]

end GlobalTheory.CompanionTheory.KerLinear
