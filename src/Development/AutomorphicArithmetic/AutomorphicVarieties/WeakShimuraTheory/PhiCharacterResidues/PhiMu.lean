module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiMu :
    ∀ {l : ℕ} [Fact l.Prime] {H Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (f : H →* Γ), Continuous f → ∀ D : Subgroup Γ, (∀ g, f g ∈ D) → ∀ g ∈ W.muG l H, f g ∈ muOf l D := by
  intro l _ H Γ _ _ _ _ _ _ f hf D hD g hg
  refine ⟨hD g, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (QuotientGroup.mk' (commutator H).topologicalClosure g) ^ l ^ k = 1 := hg
  refine ⟨k, ?_⟩
  have h1 : g ^ l ^ k ∈ (commutator H).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
    exact hk
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at h1
  rw [← map_pow, ← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
  have hle : (⊤ : Subgroup H).map f ≤ D := by
    rintro _ ⟨x, _, rfl⟩
    exact hD x
  have h3 : f '' (commutator H : Set H) ⊆ ((⁅D, D⁆ : Subgroup Γ) : Set Γ) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : f x ∈ (commutator H).map f := ⟨x, hx, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at hx'
    exact Subgroup.commutator_mono hle hle hx'
  exact closure_mono h3 (image_closure_subset_closure_image hf ⟨_, h1, rfl⟩)
