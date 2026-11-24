module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.strong_approximation_unitaryUnipotentRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)), I.IsIsot W → (∃ N : Subgroup I.GA, (N : Set I.GA) = I.NA W) ∧ IsClosed (I.NA W) ∧ (∀ m ∈ I.NA W, ((m.1, 1) : I.GA) ∈ I.NA W ∧ ((1, m.2) : I.GA) ∈ I.NA W) ∧ (∀ U : Set I.Gf, U ∈ nhds (1 : I.Gf) → ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, (γ⁻¹ * m).2 ∈ U) ∧ ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ∀ m ∈ I.NA W, ∃ γ ∈ I.GFset ∩ I.NA W, γ⁻¹ * m ∈ Cp := by
  first | exact @GlobalTheory.UnipApprox.strong_approximation | exact GlobalTheory.UnipApprox.strong_approximation | (intros; apply GlobalTheory.UnipApprox.strong_approximation <;> assumption)
