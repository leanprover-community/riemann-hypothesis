module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AutGrowth

theorem word_eq_smoothing_of_reproduced : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), IsTest (invSet E a) α → ∀ φ : Sm E a,
    smoothing ν α φ.1 = φ.1 → ∀ l : List (Lie E a), ∃ β : Lie E a → ℂ, IsTest (invSet E a) β ∧
      ((l.map (lie E a)).prod φ).1 = smoothing ν β φ.1 := by
  intro E _ _ _ a ν _ α hα φ hφ l
  induction l with
  | nil => exact ⟨α, hα, by simpa using hφ.symm⟩
  | cons X l ih =>
    obtain ⟨β, hβ, e⟩ := ih
    refine ⟨dens X β, isTest_dens X hβ, ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
    funext g
    change lieD X ((l.map (lie E a)).prod φ).1 g = _
    rw [e]
    exact lieD_smoothing ν hβ φ.2 X g

end GlobalTheory.AutGrowth
