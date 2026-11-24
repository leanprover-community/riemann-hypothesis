module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
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

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def smallBlockPlaceEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv x := by
    cases c <;> rcases x with i | j <;>
      simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv p := by
    cases c
    · by_cases h : (p : ℕ) < a
      · simp [smallBlockPlace, smallBlockOf, zIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inl, yIndex]
        ext; simp; omega
    · by_cases h : (p : ℕ) < r
      · simp [smallBlockPlace, smallBlockOf, yIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inr, zIndex]
        ext; simp; omega

theorem smallBlockPlace_eq (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem SchAntisymmetrizePlace.proof : SchAntisymmetrizePlace.Statement := by
  intro r a c Q
  set e := smallBlockPlaceEquiv r a c with he
  unfold antisymmetrize antisym

  rw [map_sum]
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) _).trans e.symm.permCongr) _ _ ?_
  intro w
  simp only [Equiv.trans_apply, Equiv.funUnique_apply]
  rw [AlgHom.map_smul_of_tower, blockPermute, rename_rename, rename_rename]
  have hs : blockSign 1 (r + a) w = ((Equiv.Perm.sign (e.symm.permCongr (w 0)) : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_permCongr, blockSign, Fintype.prod_unique]
    rfl
  rw [hs]
  congr 3
  funext x
  simp [smallBlockPlace_eq, ← he]

end

end GroundTheory.Heights₂.Heights.RestTerms
