module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowsOfExplicitParameters
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

theorem _root_.GlobalTheory.T.windows_of_explicitParameters : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C8 D.host → (∀ t, s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ 2 * s.b') → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → let η : ℝ := (D.R.m : ℝ) * (h0v s ch : ℝ); let S : ℝ := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ)); (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3) ∧ (∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ s.b ^ 2) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → s.b ≤ wj D j τ ∧ wj D j τ ≤ s.b + η + 1) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → (bT t : ℝ) + s.b' / s.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + s.b' / s.x + η) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) → s.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ s.w'' D.R.n + η) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → S ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * S) ∧ (∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧ (((D.hc τ).v i : ℚ) : ℝ) ≤ S) ∧ (∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η) ∧ 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ 10 * ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ + 20 ≤ D.host.Lw ∧ 0 < D.host.T2.card ∧ D.host.T2.card ≤ D.R.n := by
  first | exact @GlobalTheory.EX.windows_of_large_scale | exact GlobalTheory.EX.windows_of_large_scale | (intros; apply GlobalTheory.EX.windows_of_large_scale <;> assumption)
