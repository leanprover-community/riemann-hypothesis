module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIsoStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory

open NumberField

theorem toroidalCompactification_holds : GlobalTheory.Published.ToroidalCompactification := by
  intro E _ _ _ H Dw hr l Xo c
  obtain ⟨φs, hs, -⟩ := GlobalTheory.T.exists_invariant_smoothProjFan_noSelfIntersections (max 1 (Module.finrank ℚ E * min Dw.p Dw.q))
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y, -, -, -, -, -, a₁, a₂, a₃, -⟩ := GlobalTheory.Published.ToroidalForFanKS.exists_model_of_fan GlobalTheory.T.toroidalCompactificationFan_logKodairaSpencer_iso hr h₁ h₂ Xo c
  exact ⟨Y, a₁, a₂, a₃⟩

end GlobalTheory
