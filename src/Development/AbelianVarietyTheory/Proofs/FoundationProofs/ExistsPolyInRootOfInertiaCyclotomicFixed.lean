module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.InertiaCycFixed

theorem cycMod_eq_one_of_fix (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (m : ℕ) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ m)) (s : G ℚ Ω) (hs : s ζ = ζ) : cycMod ℚ Ω l m s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l (n := m)
    (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
  have hs' : (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ = ζ := hs
  rw [hs'] at hspec
  set x : ZMod (l ^ m) := ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow m)
    with hx
  have hmod : x.val ≡ 1 [MOD l ^ m] := by
    have hne : l ^ m ≠ 0 := pow_ne_zero m (Fact.out : l.Prime).ne_zero
    have hz : IsPrimitiveRoot (hζ.isUnit hne).unit (l ^ m) := IsPrimitiveRoot.isUnit_unit hne hζ
    have key := (pow_eq_pow_iff_modEq (x := (hζ.isUnit hne).unit) (n := x.val) (m := 1)).1 (by
      ext
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_one]
      exact hspec.symm)
    rwa [← hz.eq_orderOf] at key
  have h1 : ((x.val : ℕ) : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  rw [ZMod.natCast_zmod_val, Nat.cast_one] at h1
  apply Units.ext
  simpa [cycMod, cycZ, hx] using h1

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u : Ω, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ Q : Polynomial Ω, (∀ x ∈ Q.coeffs, ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ Q.eval ζ = u := by
  intro l _ Ω _ _ _ A m ζ hζ u hu
  have : IsGalois ℚ Ω := {}
  have hint : Algebra.IsIntegral ℚ Ω := Algebra.IsAlgebraic.isIntegral
  set I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A with hI
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField I with hK
  have : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  set L : IntermediateField ℚ Ω := (IntermediateField.adjoin K {ζ}).restrictScalars ℚ with hL
  have hKL : K ≤ L := fun x hx => by
    show x ∈ IntermediateField.adjoin K {ζ}
    exact (IntermediateField.adjoin K {ζ}).algebraMap_mem ⟨x, hx⟩
  have hζL : ζ ∈ L := IntermediateField.mem_adjoin_simple_self K ζ

  have hfix : ∀ s ∈ L.fixingSubgroup, s u = u := by
    intro s hs

    let C : ClosedSubgroup (G ℚ Ω) := ⟨I.topologicalClosure, I.isClosed_topologicalClosure⟩
    have hsC : s ∈ I.topologicalClosure := by
      have hle : IntermediateField.fixedField C.toSubgroup ≤ K := by
        intro x hx
        rw [IntermediateField.mem_fixedField_iff] at hx ⊢
        intro f hf
        exact hx f (I.le_topologicalClosure hf)
      have h1 : s ∈ K.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hKL hs
      have h2 := IntermediateField.fixingSubgroup_antitone hle h1
      rwa [InfiniteGalois.fixingSubgroup_fixedField C] at h2

    set E : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ {u, ζ} with hE
    have : FiniteDimensional ℚ E := by
      rw [hE]
      refine IntermediateField.finiteDimensional_adjoin ?_
      intro x _
      exact Algebra.IsIntegral.isIntegral x
    have hopen : IsOpen ((E.fixingSubgroup : Subgroup (G ℚ Ω)) : Set (G ℚ Ω)) := E.fixingSubgroup_isOpen
    have hopen' : IsOpen {x : G ℚ Ω | s⁻¹ * x ∈ E.fixingSubgroup} :=
      hopen.preimage (continuous_const.mul continuous_id)
    have hsmem : s ∈ {x : G ℚ Ω | s⁻¹ * x ∈ E.fixingSubgroup} := by
      simp only [Set.mem_ofPred_eq, inv_mul_cancel]
      exact one_mem _
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hsC
    obtain ⟨i, hi1, hi2⟩ := mem_closure_iff.1 hsC _ hopen' hsmem
    simp only [Set.mem_ofPred_eq] at hi1
    have hu' : (s⁻¹ * i) u = u :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi1 u (IntermediateField.subset_adjoin ℚ _ (by simp))
    have hζ' : (s⁻¹ * i) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hi1 ζ (IntermediateField.subset_adjoin ℚ _ (by simp))
    have hsζ : s ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ hζL
    have hiζ : i ζ = ζ := by
      have : i = s * (s⁻¹ * i) := by group
      rw [this, AlgEquiv.mul_apply, hζ', hsζ]
    have hiu : i u = u := hu i hi2 (cycMod_eq_one_of_fix l Ω m ζ hζ i hiζ)
    have : i = s * (s⁻¹ * i) := by group
    rw [this, AlgEquiv.mul_apply, hu'] at hiu
    exact hiu
  have huL : u ∈ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
    exact hfix
  have huK : u ∈ IntermediateField.adjoin K {ζ} := huL
  have hζint : IsIntegral K ζ := (Algebra.IsIntegral.isIntegral (R := ℚ) ζ).tower_top
  rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at huK
  obtain ⟨P, hP⟩ := huK
  refine ⟨P.map (algebraMap K Ω), ?_, ?_⟩
  · intro x hx s hs
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [Polynomial.coeff_map]
    exact ((IntermediateField.mem_fixedField_iff _ _).1 (P.coeff n).2) s hs
  · rw [Polynomial.eval_map_algebraMap]
    exact hP

end GlobalTheory.InertiaCycFixed
