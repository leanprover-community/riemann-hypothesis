module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeAtNearbyIndices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairSectionBallFiniteStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem lc_mono_radius {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (P : Pair p) (a b : ℤ) {R R' : ℝ} (h : R ≤ R') : P.lc a b R ≤ P.lc a b R' := by
  have hsub : P.Bl a b R ⊆ P.Bl a b R' := fun f hf => ⟨hf.1, fun σ y => (hf.2 σ y).trans h⟩
  have hfin : (P.Bl a b R').Finite := GlobalTheory.T.hermLineBundlePair_sectionBall_finite k X p D hX P a b R'
  have hle : (P.Bl a b R).ncard ≤ (P.Bl a b R').ncard := Set.ncard_le_ncard hsub hfin
  unfold VolBr.Pair.lc
  rcases Nat.eq_zero_or_pos (P.Bl a b R).ncard with h0 | h0
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hle)

theorem lc_nearby_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (P : Pair p) (b c : ℕ), 0 < b → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
      P.lc 0 (b * M + (M / n : ℕ) - c) 2 ≤ P.lc 0 (b * M - c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hX P b c hb hR ε hε
  obtain ⟨α, β, hαβ⟩ := hR
  refine GlobalTheory.eventually_le_at_nearby_indices (D + 1) b c
    (fun η j => P.lc 0 (j : ℤ) (Real.exp (η * j))) (fun j => P.lc 0 j 2) (fun j => P.lc 0 j 1) α β
    (Nat.succ_pos D) hb hαβ ?_ ?_ ε hε
  · intro j
    simp
  · intro η hη
    have ht : Tendsto (fun j : ℕ => Real.exp (η * j)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hη tendsto_natCast_atTop_atTop)
    filter_upwards [ht.eventually (eventually_ge_atTop 2)] with j hj
    exact lc_mono_radius hX P 0 (j : ℤ) hj

end GlobalTheory.HSNef
