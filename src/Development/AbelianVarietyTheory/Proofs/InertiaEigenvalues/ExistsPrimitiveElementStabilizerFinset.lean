module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem GlobalTheory.stab_finset_eq_stab_primitive : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (s : Finset Ω), ∃ β : Ω, ∀ σ : G E Ω, σ β = β ↔ ∀ x ∈ s, σ x = x := by
  intro E Ω _ _ _ _ _ s
  haveI : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  set K := IntermediateField.adjoin E (s : Set Ω) with hK
  haveI : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E K
  refine ⟨(α : Ω), fun σ => ?_⟩
  have key : IntermediateField.adjoin E {(α : Ω)} = K := by
    have h1 := congrArg (IntermediateField.map K.val) hα
    rw [IntermediateField.adjoin_map] at h1
    have hm : IntermediateField.map K.val ⊤ = K := by
      ext y; constructor
      · rintro ⟨z, -, rfl⟩; exact z.2
      · intro hy; exact ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [hm] at h1
    simpa [Set.image_singleton] using h1

  have gen : ∀ (T : Set Ω), (∀ x ∈ T, σ x = x) → ∀ y ∈ IntermediateField.adjoin E T, σ y = y := by
    intro T hT y hy
    have := IntermediateField.algHom_ext_of_eq_adjoin E (S := IntermediateField.adjoin E T) (s := T) rfl
      (φ₁ := ((σ : Ω →ₐ[E] Ω)).comp (IntermediateField.adjoin E T).val)
      (φ₂ := (IntermediateField.adjoin E T).val) (fun x hx => by simp [hT x hx])
    exact congrArg (fun φ => φ ⟨y, hy⟩) this
  constructor
  · intro h x hx
    have hxK : x ∈ IntermediateField.adjoin E {(α : Ω)} := by
      rw [key]; exact IntermediateField.subset_adjoin E _ hx
    exact gen {(α : Ω)} (by simpa using h) x hxK
  · intro h
    exact gen (s : Set Ω) (fun x hx => h x hx) (α : Ω) α.2
