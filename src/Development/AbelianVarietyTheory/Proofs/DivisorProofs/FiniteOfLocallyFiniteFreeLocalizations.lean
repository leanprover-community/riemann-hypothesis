module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LocFreeProj

theorem finite_projective_of_locally_free : ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M], (∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F) (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F) (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F) (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ) → Module.Finite R M ∧ Module.Projective R M := by
  intro R _ M _ _ h
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Free (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsLocalizedModule (Submonoid.powers r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iFree ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iFree
  haveI := hϕ
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.LocFreeProj
