module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL

namespace GlobalTheory

theorem capelli_comatrix_last_row (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → A) (hE : GlRel E) (u : ℂ) (c : Fin (n + 1)) :
    ∑ l : Fin (n + 1), (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : A) *
        (qminor E Fin.castSucc (Fin.succAbove l) (u - 1) * Tm E u c l) =
      if c = Fin.last n then qdet E u else 0 := by
  have h := Formalism.FourierDecayAlt.P.expansion_last_line A (n + 1) n E hE
    (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c) id u
  have h1 : (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c : Fin (n + 1) → Fin (n + 1)) ∘
      Fin.castSucc = Fin.castSucc := by
    funext k
    simp
  rw [h1, Fin.snoc_last] at h
  simp only [Function.id_comp, id] at h
  rw [← h]
  split_ifs with hc
  · subst hc
    unfold qdet
    congr 1
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  · obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.mpr hc
    exact quantumMinor_eq_zero_of_row_eq qSkewRow E _ _ u c'.castSucc (Fin.last n) hc (by simp)

end GlobalTheory
