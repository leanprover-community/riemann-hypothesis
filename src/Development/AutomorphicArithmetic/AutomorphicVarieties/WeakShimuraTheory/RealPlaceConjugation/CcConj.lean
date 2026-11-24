module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem emb_twist {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (i j : Ω →+* ℂ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ x, j (g x) = i x := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let iA : Ω →ₐ[ℚ] ℂ := i.toRatAlgHom
  let K : IntermediateField ℚ ℂ := jA.fieldRange
  let r : Ω →+* K :=
    { toFun := fun x => ⟨jA x, jA.mem_fieldRange.2 ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hr : Function.Bijective r := by
    constructor
    · intro x y hxy
      have : jA x = jA y := congrArg Subtype.val hxy
      exact jA.toRingHom.injective this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := jA.mem_fieldRange.1 hz
      exact ⟨x, rfl⟩
  haveI : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω K (RingEquiv.ofBijective r hr)
  have hi : ∀ x, ∃ y, j y = i x := by
    intro x
    have h1 : IsIntegral ℚ (iA x) := (Algebra.IsIntegral.isIntegral x).map iA
    have h2 : IsIntegral K (iA x) := h1.tower_top
    have h3 := minpoly.mem_range_of_degree_eq_one K (iA x)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h2))
    obtain ⟨k, hk⟩ := h3
    obtain ⟨y, hy⟩ := jA.mem_fieldRange.1 k.2
    refine ⟨y, ?_⟩
    have : jA y = iA x := by rw [hy]; exact hk
    exact this
  choose φ hφ using hi
  let h0 : Ω →+* Ω :=
    { toFun := φ
      map_one' := j.injective (by rw [hφ, map_one, map_one])
      map_mul' := fun x y => j.injective (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_zero' := j.injective (by rw [hφ, map_zero, map_zero])
      map_add' := fun x y => j.injective (by rw [hφ, map_add (f := _), map_add (f := _), hφ, hφ]) }
  let hA : Ω →ₐ[ℚ] Ω := h0.toRatAlgHom
  have hb : Function.Bijective hA := Algebra.IsAlgebraic.algHom_bijective hA
  exact ⟨AlgEquiv.ofBijective hA hb, fun x => hφ x⟩

theorem UpperTheory.V.Ws.isConj_of_isComplexConjugation :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (σ τ : G ℚ Ω), IsCC σ → IsCC τ → IsConj σ τ := by
  intro Ω _ _ _ σ τ hσ hτ
  obtain ⟨jσ, hjσ⟩ := hσ
  obtain ⟨jτ, hjτ⟩ := hτ
  obtain ⟨g, hg⟩ := emb_twist jσ jτ
  rw [isConj_iff]
  refine ⟨g, AlgEquiv.ext fun y => jτ.injective ?_⟩
  have e1 : jσ (g⁻¹ y) = jτ y := by
    rw [← hg]
    congr 1
    exact AlgEquiv.apply_symm_apply g y
  show jτ (g (σ (g⁻¹ y))) = jτ (τ y)
  rw [hg, hjσ, e1, hjτ]
