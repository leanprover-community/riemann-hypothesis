module

public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasimirNumberIdentityDualPair
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
import Formalism.SharpRestriction.Divisibility.SchurIrreducible

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

theorem _root_.GlobalTheory.T.casimir_number_identity_dualPair : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → normSq (lamA' t al be ga de) - rhoSq (al.length + be.length + ga.length + de.length + t) = normSq (lamA al be ga de) - rhoSq (al.length + be.length + ga.length + de.length) - ((al.length + be.length + ga.length + de.length : ℕ) : ℚ) * ((al.length + be.length + ga.length + de.length + t : ℕ) : ℚ) * (t : ℚ) / 4 ∧ normSq (lamM' t al be ga de) = normSq (lamA' t al be ga de) := by
  first | exact @GlobalTheory.CasimirNumber.casimir_number_identity | exact GlobalTheory.CasimirNumber.casimir_number_identity | (intros; apply GlobalTheory.CasimirNumber.casimir_number_identity <;> assumption)
