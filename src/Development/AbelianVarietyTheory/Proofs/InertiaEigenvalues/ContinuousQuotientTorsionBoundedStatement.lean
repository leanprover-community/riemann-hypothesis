module

public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientTorsionBounded
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.continuous_quotient_torsion_bounded : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] [TopologicalSpace V] [IsTopologicalAddGroup V] {X : Type} [TopologicalSpace X] [CompactSpace X] (T : Submodule O V), IsLatticeIn T → IsOpen (T : Set V) → ∀ ϖ : O, Irreducible ϖ → ∀ c : X → V ⧸ T, Continuous c → ∃ r : ℕ, ∀ x, ϖ ^ r • c x = 0 := by
  first | exact @GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | exact GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact | (intros; apply GlobalTheory.LatticeQuotBound.pow_smul_eq_zero_of_compact <;> assumption)
