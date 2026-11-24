module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.LocalSmoothExtension

private theorem exists_perm_of_map_eq {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, b (e i) = a i :=
  _root_.UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq a b h

theorem UpperTheory.Gal.LocalSmoothExtension.schWEq_of :
    SchWEq := by
  intro F _ _ n lam χ g hg
  have h : ∃ g : (F →+* ℂ) → Fin n → ℂ, Lists χ g := ⟨g, hg⟩
  unfold schW
  rw [dite_eq_left h]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨e, he⟩ := exists_perm_of_map_eq (h.choose τ) (g τ)
    ((h.choose_spec τ).symm.trans (hg τ))
  have hge : h.choose τ = g τ ∘ e := funext fun i => (he i).symm
  rw [hge]
  unfold UpperTheory.Gal.Schur.sch
  rw [← MvPolynomial.aeval_rename, GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric (lam τ) e]
