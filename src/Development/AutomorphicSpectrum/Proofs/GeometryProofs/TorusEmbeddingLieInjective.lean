module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLieLieModel
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemMaxSmulTopIff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusInjectiveLieMapStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusSat

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem pt_zero {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem exists_div {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup X] {π : R}
    (hπ : Irreducible π) (δ : X →+ R) (h : ∀ χ, IsLocalRing.residue R (δ χ) = 0) :
    ∃ δ' : X →+ R, δ = π • δ' := by
  have hd : ∀ χ, ∃ r, δ χ = π * r := fun χ => by
    have hm : δ χ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.residue_eq_zero_iff _).mp (h χ)
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ] at hm
    exact Ideal.mem_span_singleton'.mp hm |>.imp fun r hr => by rw [← hr, mul_comm]
  choose f hf using hd
  refine ⟨AddMonoidHom.mk' f fun a b => ?_, ?_⟩
  · apply mul_left_cancel₀ hπ.ne_zero
    rw [mul_add, ← hf, ← hf, ← hf, map_add (f := _)]
  · ext χ
    simp [hf]

theorem lie_torus_saturated : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (S : Scheme.{0}) (b : Sp R ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] [Smooth G.hom] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u : splitTorus S X ⟶ G) [IsMonHom u], (∀ (A : Type) [CommRing A] (g : K →+* A) (t : Over.mk (spMap g ≫ spMap (algebraMap R K) ≫ b) ⟶ splitTorus S X), t ≫ u = 1 → t = 1) → ∀ (MT : LieModel (splitTorus S X) b (X →+ R)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G b E) (A : (X →+ R) →ₗ[R] E), (∀ δ, M.pt (A δ) = MT.pt δ ≫ u) → Function.Injective A ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range A → y ∈ LinearMap.range A := by
  intro R K _ _ _ _ _ _ S b G _ _ _ _ X _ _ _ u _ hgen MT hMT E _ _ M A hA
  obtain ⟨hEf, hEp⟩ := GlobalTheory.T.lie_model_finite_projective S G R b E M
  obtain ⟨Mk, hMk⟩ := GlobalTheory.T.exists_cocharacter_lie_model S X (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨Ek, i1, i2, ⟨MG⟩⟩ := lieModel_exists S G (IsLocalRing.ResidueField R) (spMap (IsLocalRing.residue R) ≫ b)
  obtain ⟨j, hj, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S G R _ (IsLocalRing.residue R) b E Ek M MG
  obtain ⟨jT, hjT, -⟩ := LieBaseChange.existsUnique_semilinear_lifts S (splitTorus S X) R _
    (IsLocalRing.residue R) b (X →+ R) (X →+ IsLocalRing.ResidueField R) MT Mk
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hcπ : IsLocalRing.residue R π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have key : ∀ δ, A δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      δ ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R (X →+ R)) := by
    intro δ hδ
    obtain ⟨z, hz⟩ := (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mp hδ
    have h0 : j (A δ) = 0 := by
      rw [hz, map_smulₛₗ, hcπ, zero_smul]
    have a1 := hj (A δ)
    have a2 := hjT δ
    rw [Category.comp_id] at a1 a2
    rw [h0, pt_zero, hA, Over.comp_left] at a1
    have h1 : Mk.pt (jT δ) ≫ u = 1 := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, a2, Category.assoc, a1]
    have h2 : jT δ = 0 := GlobalTheory.T.torus_injective_lie_map R K S b G X u hgen Mk hMk _ h1
    have h3 : ∀ χ, IsLocalRing.residue R (δ χ) = 0 := by
      intro χ
      have e := GlobalTheory.CompanionTheory.Ar.TorusModel.charVal_comp (dualMap (IsLocalRing.residue R)) (MT.pt δ) (Mk.pt (jT δ)) a2 χ
      rw [hMk, hMT, h2] at e
      have e2 := congrArg TrivSqZeroExt.snd e
      simpa [dualMap] using e2.symm
    obtain ⟨δ', rfl⟩ := exists_div hπ δ h3
    exact (GlobalTheory.CompanionTheory.CommAlg.SatOfInj.mem_max_smul_top_iff hπ _).mpr ⟨δ', rfl⟩
  have e := addMonoidHomLequivInt (A := X) (B := R) R
  haveI : Module.Free R (X →+ R) := Module.Free.of_equiv e.symm
  haveI : Module.Finite R (X →+ R) := Module.Finite.equiv e.symm
  haveI : Module.IsTorsionFree R E := inferInstance
  exact GlobalTheory.CompanionTheory.CommAlg.SatOfInj.sat_of_inj_mod R (X →+ R) E A key

end GlobalTheory.CompanionTheory.Ar.TorusSat
