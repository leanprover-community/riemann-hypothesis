module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.IntScalars
public import GroundTheory.TateCohomology.TateTheorem
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

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem additive_addMonoidHom_int_eq_zero (f : Additive Γ →+ ℤ) : f = 0 := by
  refine AddMonoidHom.ext fun g => ?_
  have h : (Nat.card (Additive Γ) : ℤ) * f g = 0 := by
    rw [← nsmul_eq_mul, ← map_nsmul, card_nsmul_eq_zero', map_zero]
  exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 Nat.card_pos.ne')

theorem isZero_groupCohomology_one_trivial_int :
    IsZero (groupCohomology (Rep.trivial ℤ Γ ℤ) 1) := by
  refine IsZero.of_iso ?_ (H1IsoOfIsTrivial (Rep.trivial ℤ Γ ℤ))
  refine @ModuleCat.isZero_of_subsingleton _ _ _ ⟨fun f g => ?_⟩
  rw [additive_addMonoidHom_int_eq_zero f, additive_addMonoidHom_int_eq_zero g]

theorem subsingleton_groupCohomology_three_of_tate_int (M : Rep ℤ Γ) (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2 u) :
    Subsingleton (groupCohomology M 3) := by
  have hT1 : IsZero (tateCohomology (Rep.trivial ℤ Γ ℤ) ((1 : ℕ) : ℤ)) :=
    isZero_groupCohomology_one_trivial_int.of_iso
      ((TateCohomology.isoGroupCohomology 1).app (Rep.trivial ℤ Γ ℤ))
  have hT3 : IsZero (tateCohomology M (((1 : ℕ) : ℤ) + 2)) :=
    hT1.of_iso (GroundTheory.GroupCoh.tateTheoremIsoTop M u h1 h2 h3 _).symm
  have e3 : (((1 : ℕ) : ℤ) + 2) = ((3 : ℕ) : ℤ) := by norm_num
  rw [e3] at hT3
  exact ModuleCat.subsingleton_of_isZero
    (hT3.of_iso ((TateCohomology.isoGroupCohomology 3).app M).symm)

theorem subsingleton_groupCohomology_three_of_tate (M : Rep.{0} (ULift.{0} ℤ) Γ)
    (u : groupCohomology M 2)
    (h1 : ∀ S : Subgroup Γ, IsZero (groupCohomology (Rep.res S.subtype M) 1))
    (h2 : ∀ S : Subgroup Γ,
      addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) = Nat.card S)
    (h3 : ∀ (S : Subgroup Γ) (y : groupCohomology (Rep.res S.subtype M) 2),
      ∃ m : ℤ, y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype M)) 2).hom u) :
    Subsingleton (groupCohomology M 3) := by
  have H := subsingleton_groupCohomology_three_of_tate_int (uliftIntToIntRep M)
    (groupCohomologyULiftIntAddEquiv M 2 u) (fun S => ?_) (fun S => ?_) (fun S y => ?_)
  · exact (groupCohomologyULiftIntAddEquiv M 3).injective.subsingleton
  · have : Subsingleton (groupCohomology (Rep.res S.subtype M) 1) :=
      ModuleCat.subsingleton_of_isZero (h1 S)
    have : Subsingleton (groupCohomology (uliftIntToIntRep (Rep.res S.subtype M)) 1) :=
      (groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 1).symm.injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  · have e := groupCohomologyULiftIntAddEquiv_map_subtype M S 2 u
    change addOrderOf ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)) = Nat.card S
    rw [← e, AddEquiv.addOrderOf_eq]
    exact h2 S
  · obtain ⟨m, hm⟩ := h3 S ((groupCohomologyULiftIntAddEquiv (Rep.res S.subtype M) 2).symm y)
    refine ⟨m, ?_⟩
    change y = m • (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (uliftIntToIntRep M))) 2).hom
      (groupCohomologyULiftIntAddEquiv M 2 u)
    rw [← groupCohomologyULiftIntAddEquiv_map_subtype, ← map_zsmul, ← hm, AddEquiv.apply_symm_apply]

end GroundTheory.ProfCoh
