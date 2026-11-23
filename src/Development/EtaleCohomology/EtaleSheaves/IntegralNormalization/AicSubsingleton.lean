module

import Development.EtaleCohomology.EtaleSheaves.NormACPf
public import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf
import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.OpenPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.NormPf.AffPf

theorem aic_intClosure {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (h : GlobalTheory.EtC.AIC B) :
    GlobalTheory.EtC.AIC (integralClosure A B) := by
  apply LateralTheory.E.NormACPf.aic_integralClosure <;> assumption

theorem aic_field (K : Type) [Field K] [IsAlgClosed K] : GlobalTheory.EtC.AIC K := by
  intro p _ hd
  exact IsAlgClosed.exists_root p (by rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hd)]; exact_mod_cast hd.ne')

theorem aic_subsingleton (R : Type) [CommRing R] [Subsingleton R] : GlobalTheory.EtC.AIC R :=
  fun _ _ _ => ⟨0, Subsingleton.elim _ _⟩

theorem aic_specK (K : Type) [Field K] [IsAlgClosed K] (V : (Spec (CommRingCat.of K)).Opens) :
    GlobalTheory.EtC.AIC Γ(Spec (CommRingCat.of K), V) := by
  by_cases hV : (V : Set (Spec (CommRingCat.of K))).Nonempty
  · have h : V = ⊤ := by
      obtain ⟨y, hy⟩ := hV
      ext x
      simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
      have : x = y := Subsingleton.elim (α := PrimeSpectrum K) x y
      rwa [this]
    subst h
    exact OpenPf.aic_of_equiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv (aic_field K)
  · have h : V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hV ⟨x, hx⟩
    subst h
    exact aic_subsingleton _

theorem affAIC : AICPf.AffAIC := by
  intro K _ _ W g _ _ U hU
  let := (g.app U).hom.toAlgebra
  exact OpenPf.aic_of_equiv (g.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
    (aic_intClosure (aic_specK K _))

end LateralTheory.E.NormPf.AffPf

end
