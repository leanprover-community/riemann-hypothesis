module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Completeness
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem yCpl_mem {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (x : AdicCompletion (I.map (algebraMap R S)) S) :
    x ∈ (I ^ n).map (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S)) ↔
      AdicCompletion.eval (I.map (algebraMap R S)) S n x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), Ideal.smul_top_eq_map,
    ← Ideal.map_pow, Ideal.map_map, Submodule.restrictScalars_mem, ← IsScalarTower.algebraMap_eq]

private theorem yCpl_mem_of {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (s : S) :
    algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s ∈
      (I ^ n).map (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S)) ↔
      s ∈ (I ^ n).map (algebraMap R S) := by
  rw [yCpl_mem I hI, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, Submodule.mkQ_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]

theorem UpperTheory.V.Pa.Core.yCpl :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R), IsYCpl y f (AdicCompletion ((Ideal.span (Set.range y)).map (algebraMap R (Localization.Away f))) (Localization.Away f)) := by
  intro R σ _ _ _ y f
  set S := Localization.Away f
  set I : Ideal R := Ideal.span (Set.range y)
  set A := AdicCompletion (I.map (algebraMap R S)) S
  have hI : I.FG := Submodule.fg_span (Set.finite_range y)
  have hS : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
  have hRA : ∀ r : R, algebraMap R A r = algebraMap S A (algebraMap R S r) := fun r =>
    IsScalarTower.algebraMap_apply R S A r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, ?_, ?_, ?_⟩
  · rw [hRA]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  · intro n x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (I.map (algebraMap R S)) S n x)
    obtain ⟨⟨r, _, ⟨k, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers f) s
    simp only at hr
    refine ⟨k, r, ?_⟩
    have hmem : x - algebraMap S A s ∈ (I ^ n).map (algebraMap R A) := by
      rw [yCpl_mem I hI, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, ← hs,
        Algebra.algebraMap_self, RingHom.id_apply, Submodule.mkQ_apply, sub_self]
    have heq : algebraMap R A f ^ k * x - algebraMap R A r
        = algebraMap R A (f ^ k) * (x - algebraMap S A s) := by
      rw [mul_sub, hRA r, ← hr, map_mul, ← hRA (f ^ k), map_pow]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hmem
  · intro n r hr
    rw [hRA, yCpl_mem_of I hI] at hr
    obtain ⟨m, ⟨k, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S (I ^ n) r).1 hr
    exact ⟨k, hm⟩
