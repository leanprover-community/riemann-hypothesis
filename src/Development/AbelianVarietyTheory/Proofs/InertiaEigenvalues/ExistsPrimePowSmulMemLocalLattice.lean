module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LatPow

theorem pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  have hv : v ∈ Submodule.span K (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  suffices h : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : K) ^ n • v ∈ T.L.T by
    obtain ⟨n₀, h⟩ := h
    exact ⟨n₀, fun n hn => ⟨⟨_, h n hn⟩, rfl⟩⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ => ?_⟩
    have : (l : K) ^ n • x = ((l : O) ^ n) • x := by
      rw [← algebraMap_smul K ((l : O) ^ n) x, map_pow, map_natCast]
    rw [this]
    exact T.L.T.smul_mem _ hx
  | zero => exact ⟨0, fun n _ => by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun n hn => by
      rw [smul_add]
      exact T.L.T.add_mem (ha n (le_of_max_le_left hn)) (hb n (le_of_max_le_right hn))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := exists_pow_mul_mem (O := O) l c
    refine ⟨a + m, fun n hn => ?_⟩
    have e : (l : K) ^ n • c • x = b • ((l : K) ^ (n - m) • x) := by
      rw [← algebraMap_smul K b, ← hb, smul_smul, smul_smul]
      congr 1
      rw [mul_comm ((l : K) ^ m) c, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]
    rw [e]
    exact T.L.T.smul_mem _ (ha _ (by omega))

end GlobalTheory.LatPow
