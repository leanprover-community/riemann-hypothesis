module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimLEIsLocalRingQuotPow
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfMemPowMaximal
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Mathlib.RingTheory.Jacobson.Artinian
import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace ArtinReduction

theorem eq_zero_of_forall_mem_pow {R : Type} [CommRing R] [IsNoetherianRing R] (y : R)
    (hy : ∀ i : MaximalSpectrum R × ℕ, y ∈ i.1.asIdeal ^ (i.2 + 1)) : y = 0 := by
  first
  | exact @_root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
  | exact _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal
  | (apply _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> assumption)
  | (intros; apply _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EqZeroOfMemMaximalPow.eq_zero_of_mem_pow_maximal ..)

theorem krullDimLE_and_isLocalRing_quotient_pow {R : Type} [CommRing R] (m : Ideal R)
    [hm : m.IsMaximal] (n : ℕ) :
    Ring.KrullDimLE 0 (R ⧸ m ^ (n + 1)) ∧ IsLocalRing (R ⧸ m ^ (n + 1)) := by
  apply GlobalTheory.AbCoh.LowBaseChange.krullDimLE_isLocalRing_quot_pow <;> assumption

theorem exists_isGen_translDiff_comp {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T T' : Over S} (q : T' ⟶ T) (x : T ⟶ A)
    (h : ∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) :
    ∃ c : LB.Gen (Out.translDiff A L (q ≫ x)), c.IsGen := by
  obtain ⟨c, hc⟩ := h
  have h4 : ∃ w : LB.Gen (LB.LinComb L (K := Fin 2) (fun i => (q ▷ A).left ≫
      ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] i) ![1, -1]), w.IsGen :=
    ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩
  have h3 : (fun i => (q ▷ A).left ≫
      ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] i) =
      ![(lift (fst T' A ≫ q ≫ x) (snd T' A) ≫ μ[A]).left, (snd T' A).left] := by
    funext i
    fin_cases i
    · change (q ▷ A ≫ lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left =
        (lift (fst T' A ≫ q ≫ x) (snd T' A) ≫ μ[A]).left
      rw [comp_lift_assoc, whiskerRight_fst_assoc, whiskerRight_snd]
    · change (q ▷ A ≫ snd T A).left = (snd T' A).left
      rw [whiskerRight_snd]
  rw [h3] at h4
  exact h4

end ArtinReduction


open ArtinReduction in
theorem translDiff_triv_of_artin_local :
    (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → (∀ (R : Type) [CommRing R] [Algebra ℂ R], IsLocalRing R → Module.Finite ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1) → (∀ (R : Type) [CommRing R] [Algebra ℂ R], Algebra.FiniteType ℂ R → ∀ (x : Over.mk (spMap (algebraMap ℂ R)) ⟶ A), (∃ c : LB.Gen (Out.translDiff A L x), c.IsGen) → x = 1)) := by
  intro A _ L hA _ h R _ _ hR x hx
  have := hA.proper
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℂ R
  refine TorusLocal.pt_ext_of_quotients (A := ℂ) (C := R)
    (fun i : MaximalSpectrum R × ℕ => i.1.asIdeal ^ (i.2 + 1)) eq_zero_of_forall_mem_pow
    (B := A) fun i => ?_
  have := i.1.isMaximal
  obtain ⟨h1, h2⟩ := krullDimLE_and_isLocalRing_quotient_pow i.1.asIdeal i.2
  have h3 : Module.Finite ℂ (R ⧸ i.1.asIdeal ^ (i.2 + 1)) :=
    (Module.finite_iff_krullDimLE_zero ℂ _).2 h1
  exact (h _ h2 h3 _ (exists_isGen_translDiff_comp A L _ x hx)).trans (MonObj.comp_one _).symm

end GlobalTheory
