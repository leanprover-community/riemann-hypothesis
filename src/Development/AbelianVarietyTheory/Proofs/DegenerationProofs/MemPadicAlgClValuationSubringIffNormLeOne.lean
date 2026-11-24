module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.FunctionField
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

section

variable {p : ℕ} [Fact p.Prime]

theorem mem_padicAlgCl_valuationSubring_iff_norm_le_one (x : PadicAlgCl p) :
    x ∈ OO p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
  rfl

noncomputable def integralClosureToPadicAlgClIntegers
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : integralClosure ℤ_[p] K →+* OO p :=
  (K.val.toRingHom.comp (integralClosure ℤ_[p] K).val.toRingHom).codRestrict (OO p) fun x =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mpr
      ((mem_integralClosure_padicInt_iff K _).mp x.2)

theorem isLocalHom_integralClosureToPadicAlgClIntegers
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IsLocalHom (integralClosureToPadicAlgClIntegers K) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hy' : ((x : K) : PadicAlgCl p) * (y : PadicAlgCl p) = 1 :=
    congrArg (fun z : OO p => (z : PadicAlgCl p)) hy
  have h0 : (x : K) ≠ 0 := by
    intro h0
    rw [h0] at hy'
    simp at hy'
  have hinv : (x : K)⁻¹ ∈ integralClosure ℤ_[p] K := by
    rw [mem_integralClosure_padicInt_iff, IntermediateField.coe_inv,
      ← eq_inv_of_mul_eq_one_right hy']
    exact (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mp y.2
  exact IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ h0))

theorem exists_factor_integralClosure_of_finiteType {A : Type*} [CommRing A]
    [Algebra.FiniteType ℤ A] (φ : A →+* OO p) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
        ∃ ψ : A →+* integralClosure ℤ_[p] K,
          (integralClosureToPadicAlgClIntegers K).comp ψ = φ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := A)
  let φ' : A →+* PadicAlgCl p := (OO p).subtype.comp φ
  refine ⟨IntermediateField.adjoin ℚ_[p] ((s.image φ' : Finset _) : Set (PadicAlgCl p)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
    fun K hK => ?_⟩
  have hmem : ∀ a, φ' a ∈ K := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set A) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact hK (IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact K.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact K.mul_mem hx hy
  let ψ₁ : A →+* K := φ'.codRestrict K hmem
  refine ⟨ψ₁.codRestrict (integralClosure ℤ_[p] K) fun a =>
    (mem_integralClosure_padicInt_iff K _).mpr
      ((mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mp (φ a).2), ?_⟩
  ext a
  rfl

theorem exists_affineOpen_factor_of_isLocalRing {R : CommRingCat.{0}} [IsLocalRing R]
    {X : Scheme.{0}} (y : Spec R ⟶ X) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V) (φ : Γ(X, V) ⟶ R), Spec.map φ ≫ hV.fromSpec = y := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    have : y ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff).mp hz
    exact (this.ge (Set.mem_univ x) : x ∈ y ⁻¹ᵁ V)
  refine ⟨V, hV, Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr), ?_⟩
  rw [Spec.map_preimage, IsOpenImmersion.lift_fac]

end

theorem padicAlgCl_integral_points :
    (∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (z : X),
      IsClosed ({z} : Set X) → ∀ U : X.Opens, (U : Set X).Nonempty →
        ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ X),
          y (cPt p) = z ∧ Set.range (gPt p ≫ y) ⊆ U) ∧
    (∀ (X : Scheme.{0}) (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π] (p : ℕ) [Fact p.Prime]
      (y : Sp (OO p) ⟶ X), ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p),
        FiniteDimensional ℚ_[p] K₀ ∧ ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
          ∃ (j : integralClosure ℤ_[p] K →+* OO p) (y₀ : Sp (integralClosure ℤ_[p] K) ⟶ X),
            (∀ x, ((j x : OO p) : PadicAlgCl p) = ((x : K) : PadicAlgCl p)) ∧ IsLocalHom j ∧
              spMap j ≫ y₀ = y) := by
  refine ⟨fun X _ π _ _ z hz U hU => ?_, fun X π _ p _ y => ?_⟩
  · obtain ⟨p, hp, hpz⟩ := exists_prime_residueField_eq_zero π hz
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨K, hK, y, hy, hyU, -⟩ := exists_padic_point_scheme π hz hpz U hU
    haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
    refine ⟨p, inferInstance, spMap (integralClosureToPadicAlgClIntegers K) ≫ y, ?_, ?_⟩
    · refine (Scheme.Hom.comp_apply _ _ _).trans ((congrArg y ?_).trans hy)
      exact IsLocalRing.comap_closedPoint (integralClosureToPadicAlgClIntegers K)
    · rintro _ ⟨x, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply]
      have key : spMap (integralClosureToPadicAlgClIntegers K) ((gPt p) x) =
          genericPoint (Sp (integralClosure ℤ_[p] K)) := by
        rw [genericPoint_eq_bot_of_affine]
        apply PrimeSpectrum.ext
        apply le_antisymm _ bot_le
        intro a ha
        have ha' : ((a : K) : PadicAlgCl p) ∈ (x : PrimeSpectrum (PadicAlgCl p)).asIdeal := ha
        haveI := (x : PrimeSpectrum (PadicAlgCl p)).isPrime
        rw [Ideal.eq_bot_of_prime (x : PrimeSpectrum (PadicAlgCl p)).asIdeal,
          Ideal.mem_bot] at ha'
        exact Subtype.ext (Subtype.ext ha')
      rw [Scheme.Hom.comp_apply, key]
      exact hyU
  · obtain ⟨V, hV, φ, rfl⟩ := exists_affineOpen_factor_of_isLocalRing y
    haveI := finiteType_int_sections π hV
    obtain ⟨K₀, hK₀, H⟩ := exists_factor_integralClosure_of_finiteType φ.hom
    refine ⟨K₀, hK₀, fun K hK => ?_⟩
    obtain ⟨ψ, hψ⟩ := H K hK
    refine ⟨integralClosureToPadicAlgClIntegers K,
      Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec, fun _ => rfl,
      isLocalHom_integralClosureToPadicAlgClIntegers K, ?_⟩
    rw [← Category.assoc]
    congr 1
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a
    exact congrArg (fun f => ((f a : OO p) : PadicAlgCl p)) hψ

end GlobalTheory
