module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res
  pullback_map_app_pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.FlagLocal

variable {X Y S : Scheme.{0}} {A A' A'' E E' : X.Modules}

theorem bijective_pullbackSections (a : Y ⟶ X) [IsOpenImmersion a] (E : X.Modules) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) :
    Function.Bijective (pullbackSections a E hW.le) := by
  subst hW
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction a) E
  have h1 : Function.Bijective (E.presheaf.map (homOfLE (a.image_preimage_le V)).op) :=
    QCoh.res_bijective_of_eq E _ (by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]; exact inf_eq_right.2 hV)
  have h2 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctorIsoPullback a).hom.app E).app (a ⁻¹ᵁ V))
  convert h2.comp h1 using 1
  funext s
  exact (resM_self _ _).trans congr(($e).app V s).symm

theorem mem_range_of_pullback (a : Y ⟶ X) [IsOpenImmersion a] (v : A ⟶ E) {V : X.Opens}
    (hV : V ≤ a.opensRange) {W : Y.Opens} (hW : W = a ⁻¹ᵁ V) (t : Γ(E, V))
    (h : ∃ m, ((Scheme.Modules.pullback a).map v).app W m = pullbackSections a E hW.le t) :
    ∃ m, v.app V m = t := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨m, rfl⟩ := (bijective_pullbackSections a A hV hW).2 m
  rw [pullback_map_app_pullbackSections] at hm
  exact ⟨m, (bijective_pullbackSections a E hV hW).1 hm⟩

section Cover

variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

variable {G : ∀ i, (T i).Modules} (v : ∀ i, G i ⟶ (Scheme.Modules.pullback (a i)).obj E)


end Cover

end GlobalTheory.FlagLocal
