module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLatticePairProjectionSmulUnits
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

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.stableLatticePair_projection_smul_units : ∀ (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)), latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  first | exact @GlobalTheory.UnitLemma.latProj_smul | exact GlobalTheory.UnitLemma.latProj_smul | (intros; apply GlobalTheory.UnitLemma.latProj_smul <;> assumption)
