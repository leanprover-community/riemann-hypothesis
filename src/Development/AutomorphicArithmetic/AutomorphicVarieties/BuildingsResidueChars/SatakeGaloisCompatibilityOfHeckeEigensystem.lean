module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.satake_galois_compatibility_of_hecke_eigensystem :
    HypothesesH → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (satLoc P E a w σ).2 _ π.finPart ((locCompC P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P E a π w
    ⟨σ, hi σ hσ⟩
