module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
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
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem openSubgroups_finite_of_fields_finite :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Set (HeightOneSpectrum (𝓞 F))),
      (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
        Module.finrank F E ≤ N}.Finite) →
      ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) |
        IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S hfin N
  haveI : IsGalois F Ω := IsSepClosure.isGalois
  let K := maxUnramifiedOutside F Ω S
  let φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω :=
    fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))
  have key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) →
      (IntermediateField.fixedField H).fixingSubgroup = H := fun H hH =>
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  apply Set.Finite.of_finite_image (f := φ)
  · apply (hfin N).subset
    rintro _ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩
    have hfix := key H hHo
    have hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F))) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)
    let e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H) :=
      IntermediateField.equivMap _ (IntermediateField.val K)
    haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine ⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2
      (IntermediateField.lift_le _), ?_⟩
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hHN
  · intro H₁ h₁ H₂ h₂ h
    have h' := IntermediateField.lift_injective K h
    exact (key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))

end GlobalTheory.CompanionTheory.GlobalFiniteness
