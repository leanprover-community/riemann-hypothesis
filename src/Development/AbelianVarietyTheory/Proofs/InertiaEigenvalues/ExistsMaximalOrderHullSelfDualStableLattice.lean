module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullLat

theorem fg_of_le {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {L X : Submodule R M} (hL : L.FG) (hX : X ≤ L) : X.FG := by
  haveI : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : (X.comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hX] at h2

theorem exists_hull : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x,
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧
      (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧
      (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
        (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by
  intro K B x c hc L hL hcL
  obtain ⟨⟨hfg, hspan⟩, -, hdual⟩ := hL
  set Λ := Subalgebra.toSubmodule (integralClosure K.O B.A) with hΛ
  set J : Submodule K.O B.A := Λ * L with hJ
  set γ := algebraMap K.O B.A c with hγ

  have hγu : IsUnit γ := by
    have h0 : algebraMap K.O K.E c ≠ 0 := by
      intro h; exact hc (IsFractionRing.injective K.O K.E (by simpa using h))
    rw [hγ, IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (isUnit_iff_ne_zero.mpr h0).map (algebraMap K.E B.A)
  have hLJ : L ≤ J := fun y hy => by
    simpa using Submodule.mul_mem_mul (M := Λ) (N := L)
      (show (1 : B.A) ∈ Λ from (integralClosure K.O B.A).one_mem) hy
  have hcJ : ∀ y ∈ J, γ * y ∈ L := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu l hl
      rw [← mul_assoc]
      exact hcL u ((mem_integralClosure_iff _ _).mp hu) l hl
    · intro a b ha hb
      rw [mul_add]; exact add_mem ha hb
  have hmulJ : mulLat K.O γ J ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcJ y hy

  have hJfg : J.FG := by
    obtain ⟨u, hu⟩ := hγu
    have hM : (L.map (LinearMap.mulLeft K.O ((u⁻¹ : B.Aˣ) : B.A))).FG := hfg.map _
    refine fg_of_le hM ?_
    intro y hy
    refine ⟨γ * y, hcJ y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨J, ⟨hJfg, ?_⟩, ?_, ?_, ?_, hmulJ, hLJ⟩
  · rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono hLJ
  · intro a ha y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu l hl
      rw [← mul_assoc]
      have hu' : u ∈ integralClosure K.O B.A := hu
      exact Submodule.mul_mem_mul (show a * u ∈ Λ from (integralClosure K.O B.A).mul_mem ha hu') hl
    · intro p q hp hq
      rw [mul_add]; exact add_mem hp hq
  · intro y hy
    exact hLJ ((hdual y).mpr fun z hz => hy z (hLJ hz))
  · intro y hy z hz
    exact (hdual (γ * y)).mp (hcJ y hy) (γ * z) (hcJ z hz)

end GlobalTheory.HullLat
