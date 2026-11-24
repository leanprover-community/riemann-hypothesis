module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalL2BoundHeight
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

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.local_L2_bound_height : ∀ (B : RowsAut) (U : Set B.I.GA), 1 ≤ B.I.n → IsCompact U → (∀ u ∈ U, u.2 ∈ B.I.Kset) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : B.I.L2 B.μf B.fund) (x : B.I.GA), ∫⁻ g in U, (‖B.I.ext y (x * g)‖₊ : ENNReal) ^ 2 ∂(B.I.muA B.μf) ≤ ENNReal.ofReal (C * (tau1 B.I x)⁻¹ ^ (4 * B.I.n ^ 2 * B.I.f) * ‖y‖ ^ 2) := by
  first | exact @GlobalTheory.LocMass.local_mass_le | exact GlobalTheory.LocMass.local_mass_le | (intros; apply GlobalTheory.LocMass.local_mass_le <;> assumption)
