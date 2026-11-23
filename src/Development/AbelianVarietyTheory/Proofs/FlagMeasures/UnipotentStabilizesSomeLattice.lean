module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem exists_fg_span_stable_of_unipotent {E : Type} [CommRing E] (O : Subring E) {n : ℕ}
    (g : (Fin n → E) →ₗ[E] (Fin n → E)) (e : ℕ) (hg : (g - 1) ^ e = 0) :
    ∃ Λ : Submodule O (Fin n → E), Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧
      (∀ v ∈ Λ, g v ∈ Λ) ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g w = v := by
  set x : (Fin n → E) →ₗ[E] (Fin n → E) := 1 - g with hx
  have hxe : x ^ e = 0 := by
    have : x = -(g - 1) := by rw [hx, neg_sub]
    rw [this, neg_pow, hg, mul_zero]
  let s : Set (Fin n → E) :=
    Set.range fun p : Fin (e + 1) × Fin n => (x ^ (p.1 : ℕ)) (Pi.single p.2 1)
  have hall : ∀ (i : ℕ) (j : Fin n), (x ^ i) (Pi.single j 1) ∈ Submodule.span O s := by
    intro i j
    by_cases hi : i < e + 1
    · exact Submodule.subset_span ⟨(⟨i, hi⟩, j), rfl⟩
    · have : x ^ i = 0 := pow_eq_zero_of_le (by omega) hxe
      rw [this]
      exact Submodule.zero_mem _
  have hpow : ∀ (k : ℕ), ∀ v ∈ Submodule.span O s, (x ^ k) v ∈ Submodule.span O s := by
    intro k v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have := hall (k + p.1) p.2
      rwa [pow_add, Module.End.mul_apply] at this
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (x ^ k) (c • a) = c • (x ^ k) a := (x ^ k).map_smul (c : E) a
      rw [this]
      exact Submodule.smul_mem _ c ha
  refine ⟨Submodule.span O s, Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_⟩
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    have := hall 0 j
    simpa using this
  · intro v hv
    have h1 := hpow 1 v hv
    have h2 : g v = v - (x ^ 1) v := by simp [hx]
    rw [h2]
    exact Submodule.sub_mem _ hv h1
  · intro v hv
    refine ⟨(∑ i ∈ Finset.range e, x ^ i) v, ?_, ?_⟩
    · rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hpow i v hv
    · have h := mul_neg_geom_sum x e
      have h1 : 1 - x = g := by rw [hx, sub_sub_cancel]
      rw [h1, hxe, sub_zero] at h
      rw [← Module.End.mul_apply, h, Module.End.one_apply]

theorem exists_isLat_stabL_of_unipotent : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (g : ((Fin n → E) ≃ₗ[E] (Fin n → E))) (e : ℕ), (((g : (Fin n → E) →ₗ[E] (Fin n → E)) - 1) ^ e = 0) → ∃ Λ : Submodule L.O (Fin n → E), IsLat L Λ ∧ g ∈ stabL L Λ := by
  intro F _ _ _ _ _ E _ _ _ L n g e hg
  obtain ⟨Λ, h1, h2, h3, h4⟩ := exists_fg_span_stable_of_unipotent L.O _ e hg
  refine ⟨Λ, ⟨h1, h2⟩, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact h3 w hw
  · intro hv
    obtain ⟨w, hw, h⟩ := h4 v hv
    exact ⟨w, hw, h⟩

end GlobalTheory.HL
