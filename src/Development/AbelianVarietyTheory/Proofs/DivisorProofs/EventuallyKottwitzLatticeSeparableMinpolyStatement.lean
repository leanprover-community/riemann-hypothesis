module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  first | (exact @GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (exact GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (intros; apply GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep  <;> assumption)
