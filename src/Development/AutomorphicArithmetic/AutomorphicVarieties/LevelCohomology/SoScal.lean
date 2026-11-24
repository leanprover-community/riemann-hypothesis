module

public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
import Formalism.GaloisCohomology.Statement

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private def subEq {R R' X : Type} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [Module R' X]
    (Z : Submodule R X) (Z' : Submodule R' X) (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') : Z ≃+ Z' where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem quotEq {R R' X : Type} [CommRing R] [CommRing R'] [AddCommGroup X] [Module R X] [Module R' X]
    (Z B : Submodule R X) (Z' B' : Submodule R' X)
    (hZ : ∀ x, x ∈ Z ↔ x ∈ Z') (hB : ∀ x, x ∈ B ↔ x ∈ B') :
    Nonempty ((Z ⧸ B.comap Z.subtype) ≃+ (Z' ⧸ B'.comap Z'.subtype)) := by
  refine ⟨QuotientAddGroup.congr (B.comap Z.subtype).toAddSubgroup (B'.comap Z'.subtype).toAddSubgroup (subEq Z Z' hZ) ?_⟩
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hB _).1 hy
  · intro hx
    exact ⟨⟨x.1, (hZ _).2 x.2⟩, (hB _).2 hx, rfl⟩

theorem UpperTheory.V.X.So.scal :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (M : Type) [AddCommGroup M] [Module R M] [Module R' M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (ρ' : Representation R' Γ M), (∀ g m, ρ g m = ρ' g m) → Nonempty (H0 ρ ≃+ H0 ρ') ∧ Nonempty (H1 ρ ≃+ H1 ρ') ∧ Nonempty (H2 ρ ≃+ H2 ρ') := by
  intro R R' _ _ Γ _ _ M _ _ _ _ _ ρ ρ' h
  have hd : ∀ c, d1 ρ c = d1 ρ' c := by
    intro c
    funext p
    obtain ⟨g, k⟩ := p
    rw [d1_apply, d1_apply, h]
  refine ⟨⟨subEq _ _ fun x => ?_⟩, quotEq _ _ _ _ (fun x => ?_) (fun x => ?_),
    quotEq _ _ _ _ (fun x => ?_) (fun x => ?_)⟩
  · simp only [mem_riemannRochSpace_iff_regularAt_everywhere, h]
  · simp only [mem_Z1_iff_cocycle, h]
  · simp only [mem_coboundaries1, h]
  · simp only [mem_cocycles2, h]
  · simp only [separated_dvr_second_cohomology_mem, hd]
