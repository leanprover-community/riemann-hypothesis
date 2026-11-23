module

public import Mathlib.Algebra.DualNumber
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndRelDimOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SubsingletonSpDualNumber
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualRigidityField

theorem subsingleton_sp_dualNumber (K : Type) [Field K] : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    have hn : IsNilpotent x := by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst]
      have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
      have h0 : x.fst = 0 := by simpa using this
      rw [h0]; exact IsNilpotent.zero
    obtain ⟨n, hn⟩ := hn
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem eq_of_eq_closedFibre {K : Type} [Field K] (A' G' : Over (Sp (DualNumber K))) [GrpObj A'] [GrpObj G']
    (a b : A' ⟶ G') (hA : IsAbelianScheme A')
    (hab : pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ a.left =
      pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ b.left)
    (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  haveI := subsingleton_sp_dualNumber K
  let j := pullback.fst A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
  have hj : IsPullback j (pullback.snd A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)) A'.hom
      (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := IsPullback.of_hasPullback _ _
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (GlobalTheory.globalFns_holds _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

theorem pullback_eq : ∀ {R : Type} [CommRing R] (k : Type) [Field k] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (f : R →+* DualNumber k) (π₁ π₂ : B'.left ⟶ A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsGrpPullback B' A (spMap f) π₁ → IsGrpPullback B' A (spMap f) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ = π₂ := by
  intro R _ k _ A _ g B' _ f π₁ π₂ hA hg h1 h2 hx
  have hB := (GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f A B' π₂ g h2 hA hg).1
  let α : B' ⟶ B' := Over.homMk (h2.1.lift π₁ B'.hom h1.1.w) (h2.1.lift_snd _ _ _)
  have hα : α.left ≫ π₂ = π₁ := h2.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom h1 h2 (𝟙 A) α (by rw [hα]; rfl)
  have hα1 : α = 𝟙 B' := by
    refine eq_of_eq_closedFibre B' B' α (𝟙 B') hB ?_ (by rw [IsMonHom.one_hom, Category.comp_id])
    apply h2.1.hom_ext
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [hα]
      exact hx _ _ _ pullback.condition
    · simp only [Category.assoc, Over.id_left, Category.comp_id]
      rw [Over.w α]
  rw [← hα, hα1, Over.id_left, Category.id_comp]

end GlobalTheory.DualRigidityField
