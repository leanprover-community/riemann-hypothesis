module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMHStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordBoxStatement
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

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_T1_and_J1_mem_window_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → (pageWord L j ε τ φ).T1 ∧ ∀ i, ∀ u ∈ (pageWord L j ε τ φ).J1 i, -((pageWord L j ε τ φ).Mi i : ℤ) ≤ u ∧ u ≤ (pageWord L j ε τ φ).hi i := by
  intro D L C j ε τ φ hR
  have hT : (pageWord L j ε τ φ).T1 := by
    intro i u hu
    exact GlobalTheory.T.twistedDualJumps_mem_windows (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) L.Sc L.etaSz
      (fun a => L.cloud_v _ a) (fun a => L.be_close _ a j) u hu
  refine ⟨hT, GlobalTheory.T.jumps_mem_box_neg_M_h _ (fun i => ?_) hT⟩
  have h := (GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ φ hR).2.2.2.2.2 i
  exact le_trans (Int.natCast_nonneg _) h.le

end GlobalTheory.HTW
