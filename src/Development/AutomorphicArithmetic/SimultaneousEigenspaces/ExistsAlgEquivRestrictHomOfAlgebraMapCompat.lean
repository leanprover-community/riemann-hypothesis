module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

theorem UpperTheory.exists_algEquiv_restrict_hom_of_algebraMap_compat :
    ∀ (k K Ω Ω' : Type) [Field k] [Field K] [Field Ω] [Field Ω'] [Algebra k Ω] [IsAlgClosure k Ω] [Algebra K Ω'] (τ : k →+* K) (j : Ω →+* Ω'), (∀ x, j (algebraMap k Ω x) = algebraMap K Ω' (τ x)) → ∃ r : (Ω' ≃ₐ[K] Ω') →* (Ω ≃ₐ[k] Ω), ∀ σ' x, σ' (j x) = j (r σ' x) := by
  intro k K Ω Ω' _ _ _ _ _ _ _ τ j hj
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have key : ∀ (s : Ω' ≃ₐ[K] Ω') (x : Ω), ∃ y, s (j x) = j y := by
    intro s x
    have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
    have hP : ((minpoly k x).map (algebraMap k Ω)).Splits := IsAlgClosed.splits _
    have hPm : ((minpoly k x).map (algebraMap k Ω)).map j = ((minpoly k x).map τ).map (algebraMap K Ω') := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext c
      exact hj c
    have hne : ((minpoly k x).map (algebraMap k Ω)).map j ≠ 0 :=
      Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
    have h0 : (((minpoly k x).map (algebraMap k Ω)).map j).eval (j x) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
    have hroot : s (j x) ∈ (((minpoly k x).map (algebraMap k Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne]
      show Polynomial.eval _ _ = 0
      rw [hPm, Polynomial.eval_map_algebraMap,
        show s (j x) = (s : Ω' →ₐ[K] Ω') (j x) from rfl, Polynomial.aeval_algHom_apply,
        ← Polynomial.eval_map_algebraMap, ← hPm, h0, map_zero]
    rw [hP.roots_map_of_ne_zero hne, Multiset.mem_map] at hroot
    obtain ⟨y, -, hy⟩ := hroot
    exact ⟨y, hy.symm⟩
  choose g hg using key
  have hji : Function.Injective j := j.injective
  let gA : (Ω' ≃ₐ[K] Ω') → (Ω →ₐ[k] Ω) := fun s =>
    { toFun := g s
      map_one' := hji (by rw [← hg]; simp only [map_one])
      map_mul' := fun a b => hji (by rw [← hg]; simp only [map_mul, hg])
      map_zero' := hji (by rw [← hg]; simp only [map_zero])
      map_add' := fun a b => hji (by rw [← hg]; simp only [map_add (f := _), hg])
      commutes' := fun c => hji (by rw [← hg, hj, AlgEquiv.commutes]) }
  let r : (Ω' ≃ₐ[K] Ω') → (Ω ≃ₐ[k] Ω) := fun s => (Algebra.IsAlgebraic.algEquivEquivAlgHom k Ω).symm (gA s)
  have hr : ∀ s x, r s x = g s x := fun s x => rfl
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext x
    apply hji
    rw [hr, ← hg]
    simp
  · intro s t
    ext x
    apply hji
    rw [hr, ← hg, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hr, hr]
    simp only [hg]
  · intro s x
    show s (j x) = j (r s x)
    rw [hr, hg]
