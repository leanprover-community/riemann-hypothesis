module

import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
public import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LocalThickGlue

theorem subsingleton_primeSpectrum (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    Subsingleton (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))) := by
  let q := Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hr := range_comap_of_surjective _ q hq
  dsimp [q] at hr
  rw [Ideal.mk_ker, PrimeSpectrum.zeroLocus_pow _ (Nat.succ_ne_zero e),
    PrimeSpectrum.zeroLocus_eq_singleton] at hr
  refine ⟨fun P Q => PrimeSpectrum.comap_injective_of_surjective q hq ?_⟩
  exact Set.subsingleton_singleton (hr ▸ Set.mem_range_self P) (hr ▸ Set.mem_range_self Q)

theorem pow_succ_ne_top (R : Type) [CommRing R] [IsLocalRing R] (e : ℕ) :
    IsLocalRing.maximalIdeal R ^ (e + 1) ≠ ⊤ := fun h =>
  (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero e)))

theorem exists_glue : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R →
    ∀ (X : Scheme.{0}) (x : ∀ e : ℕ, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) ⟶ X),
    (∀ e, Out.thickTrans R (IsLocalRing.maximalIdeal R) e ≫ x (e + 1) = x e) →
    ∃ f : Sp R ⟶ X, ∀ e, Out.thick R (IsLocalRing.maximalIdeal R) e ≫ f = x e := by
  intro R _ _ hc X x hx
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := hc
  haveI hnt : ∀ e, Nontrivial (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Ideal.Quotient.nontrivial_iff.2 (pow_succ_ne_top R e)
  haveI hss := subsingleton_primeSpectrum R
  let z : ∀ e, Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    (Classical.arbitrary (PrimeSpectrum (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))))
  have hpt : ∀ e (a : Sp (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1))), x e a = x 0 (z 0) := by
    intro e
    induction e with
    | zero => intro a; rw [Subsingleton.elim (α := PrimeSpectrum _) a (z 0)]
    | succ n ih =>
      intro a
      rw [Subsingleton.elim (α := PrimeSpectrum _) a (Out.thickTrans R (IsLocalRing.maximalIdeal R) n (z n))]
      have e1 := congrArg (fun h => h (z n)) (hx n)
      simp only [Scheme.Hom.comp_apply] at e1
      rw [e1, ih]
  obtain ⟨U, hU, hqU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x 0 (z 0) ∈ (⊤ : X.Opens) from trivial)
  have hU' : IsAffineOpen U := hU
  have hr : ∀ e, Set.range (x e) ⊆ Set.range hU'.fromSpec := by
    intro e
    rw [hU'.range_fromSpec]
    rintro _ ⟨a, rfl⟩
    rw [hpt e a]
    exact hqU
  let ρ : ∀ e, Γ(X, U) ⟶ CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (e + 1)) := fun e =>
    Spec.preimage (IsOpenImmersion.lift hU'.fromSpec (x e) (hr e))
  have hρ : ∀ e, Spec.map (ρ e) ≫ hU'.fromSpec = x e := fun e => by
    simp only [ρ, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ e, (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))).comp (ρ (e + 1)).hom =
      (ρ e).hom := fun e => by
    have h1 : ρ (e + 1) ≫ CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))) =
        ρ e := by
      apply Spec.map_injective
      rw [← cancel_mono hU'.fromSpec, Spec.map_comp, Category.assoc, hρ, hρ]
      exact hx e
    exact congrArg CommRingCat.Hom.hom h1
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  let F : Γ(X, U) →+* R := IsAdicComplete.StrictMono.liftRingHom (IsLocalRing.maximalIdeal R) ha
    (fun n => (ρ n).hom) (fun {n} => hcomp n)
  refine ⟨Spec.map (CommRingCat.ofHom F) ≫ hU'.fromSpec, fun e => ?_⟩
  have hF : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (e + 1))).comp F = (ρ e).hom :=
    IsAdicComplete.StrictMono.mk_comp_liftRingHom (IsLocalRing.maximalIdeal R) ha _ _
  rw [← hρ e, ← Category.assoc]
  congr 1
  rw [Out.thick, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hF]
  rfl

end GlobalTheory.LocalThickGlue
