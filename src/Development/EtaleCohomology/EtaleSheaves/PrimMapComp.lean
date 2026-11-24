module

public import Development.EtaleCohomology.EtaleSheaves.AcycQAPf
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.AcycQAPf

namespace LateralTheory.E.Deg0Pf

theorem exists_prim (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hA : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  obtain ⟨z, hz⟩ : ∃ z : S, (Polynomial.cyclotomic q S).eval z = 0 := by
    rcases subsingleton_or_nontrivial S with hs | hs
    · exact ⟨0, Subsingleton.elim _ _⟩
    · exact hA _ (Polynomial.cyclotomic.monic q S) (by
        rw [Polynomial.natDegree_cyclotomic]
        exact Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q)))
  refine ⟨⟨z, hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (ζ : Prim q A) : (ζ.map f).map g = ζ.map (g.comp f) := rfl

theorem rL_comp {S : Type} [CommRing S] (f g : S) :
    (rL f g).comp (algebraMap S (Localization.Away f)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayRight_eq f g a

theorem rR_comp {S : Type} [CommRing S] (f g : S) :
    (rR f g).comp (algebraMap S (Localization.Away g)) = algebraMap S (Localization.Away (f * g)) := by
  ext a; exact IsLocalization.Away.awayToAwayLeft_eq g f a

theorem Deg0_of : LateralTheory.E.AcycQAPf.Deg0 := by
  intro hQ hH hL h9 q _ i S _ hS hq f g hfg c
  obtain ⟨e, he⟩ := hH h9 q i
  obtain ⟨ζ⟩ := exists_prim q S (hQ S hS).1 hq
  obtain ⟨a, b, hab⟩ := hL q S hS f g hfg ((e _ (ζ.map (algebraMap S (Localization.Away (f * g))))).symm c)
  refine ⟨e _ (ζ.map (algebraMap S (Localization.Away f))) a, e _ (ζ.map (algebraMap S (Localization.Away g))) b, ?_⟩
  rw [he, he, prim_map_comp, prim_map_comp, rL_comp, rR_comp, ← map_sub, ← hab, AddEquiv.apply_symm_apply]

end LateralTheory.E.Deg0Pf
