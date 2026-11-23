module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDcOfCover
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DoubleCosetMassEqRelIndexMulMass
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.UnimodMass

theorem _root_.GlobalTheory.T.doubleCosetMass_eq_relIndex_mul_mass : ∀ (G : Type) [Group G] (Γ W K : Subgroup G), W ≤ K → Finite (GlobalTheory.UnimodMass.DC Γ W) → (∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) → W.relIndex K ≠ 0 ∧ GlobalTheory.UnimodMass.mass Γ W = (W.relIndex K : ℚ) * GlobalTheory.UnimodMass.mass Γ K := by
  first | exact @GlobalTheory.UnimodMass.mass_eq_relIndex_mul | exact GlobalTheory.UnimodMass.mass_eq_relIndex_mul | (intros; apply GlobalTheory.UnimodMass.mass_eq_relIndex_mul <;> assumption)
