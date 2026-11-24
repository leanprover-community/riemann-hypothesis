module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianLifting
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLiftingOfDeRhamUnobstructed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamStructureOfCubeDualPoincareStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomologyStatement
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

theorem GlobalTheory.SqLift.abelianLifting_of_known_theorems :
    GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.DualAbelianScheme →
      GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.Published.AbelianUnobstructed →
      GlobalTheory.Published.AbelianLifting :=
  fun a b c d e =>
    GlobalTheory.SqLift.abelianLifting_of_schemeLifts (GlobalTheory.T.abelianSchemeDeRhamStructure_of_cube_dual_poincare a b c d) (GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology a) e
