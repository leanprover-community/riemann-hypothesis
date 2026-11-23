module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
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

@[expose] public section

open PositivityTheory.RgBcC.RealD (kF)

namespace GlobalTheory.CompanionTheory.ModelS

theorem eq_smul_of_commute_of_ev : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  intro n V _ _ F1 F2 hfin z hz ev c hev hS x
  set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
  set y : V := z x - c • x with hy
  obtain ⟨S₁, hfd, hyS₁, hst⟩ := hfin y
  have hpres : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      exact hst a b
    | algebraMap r =>
      intro w hw
      simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
    | add S T _ _ hS' hT' =>
      intro w hw
      exact S₁.add_mem (hS' w hw) (hT' w hw)
    | mul S T _ _ hS' hT' =>
      intro w hw
      exact hS' _ (hT' w hw)
  have hcomm : ∀ T ∈ A, z * T = T * z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      have h1 := (hz a b).1
      have h2 := (hz a b).2
      show z * (F1 a b + F2 a b) = (F1 a b + F2 a b) * z
      rw [mul_add, add_mul, h1, h2]
    | algebraMap r => exact (Algebra.commutes r z).symm
    | add S T _ _ hS' hT' => rw [mul_add, add_mul, hS', hT']
    | mul S T _ _ hS' hT' => rw [← mul_assoc, hS', mul_assoc, hT', mul_assoc]
  let S : Submodule ℂ V := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ y)
  have hmem : ∀ w, w ∈ S ↔ ∃ T ∈ A, T y = w := by
    intro w
    simp [S, Submodule.mem_map]
  have hle : S ≤ S₁ := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    exact hpres T hT y hyS₁
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  have hSst : ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
  have hSev : ∀ w ∈ S, ev w = 0 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    have hzT : T (z x) = z (T x) := (LinearMap.congr_fun (hcomm T hT) x).symm
    rw [hy, map_sub, map_smul, hzT, map_sub, map_smul, hev, smul_eq_mul, sub_self]
  have hyS : y ∈ S := (hmem y).2 ⟨1, A.one_mem, rfl⟩
  exact sub_eq_zero.1 (hS S hSfd hSst hSev y hyS)

end GlobalTheory.CompanionTheory.ModelS
