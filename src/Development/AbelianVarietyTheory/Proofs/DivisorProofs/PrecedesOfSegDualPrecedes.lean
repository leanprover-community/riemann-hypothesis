module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocLanglands

theorem precedes_of_segDual_precedes :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∀ D : IrrGL (k := k) → IrrGL (k := k), (∀ x y, DualCl x y ↔ y = D x) → (∀ x, D (D x) = x) →
      (∀ (x : IrrGL (k := k)) (s : ℂ), D (x.nu s) = (D x).nu (-s)) → (∀ x, x.IsCusp → (D x).IsCusp) →
      (∀ x, (D x).1 = x.1) → ∀ Δ Γ Δ' Γ' : Segment k, SegDual Δ Δ' → SegDual Γ Γ' → Γ'.Precedes Δ' → Δ.Precedes Γ := by
  intro k _ _ _ _ D hD hDD hnu _ _ Δ Γ Δ' Γ' ⟨l1, d1⟩ ⟨l2, d2⟩ H
  obtain ⟨j, h0, h1, h2, e⟩ := Segment.precedes_iff.1 H
  rw [(hD _ _).1 d1, (hD _ _).1 d2] at e
  have e' := congrArg D e
  rw [hnu (D _), hDD, hDD, IrrGL.nu_nu] at e'
  rw [l1] at h2
  rw [l2] at h1 h2
  obtain ⟨i, hi⟩ : ∃ i : ℕ, j + Δ.len = Γ.len + i := ⟨j + Δ.len - Γ.len, by omega⟩
  refine Segment.precedes_iff.2 ⟨i, by omega, by omega, by omega, ?_⟩
  have hc : (j : ℂ) + Δ.len = Γ.len + i := by exact_mod_cast hi
  have e2 := congrArg (fun x => IrrGL.nu x (-((Γ.len : ℂ) - 1 + -(j : ℂ)))) e'
  simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at e2
  rw [← e2]
  congr 1
  linear_combination hc

end GlobalTheory.LocLanglands
