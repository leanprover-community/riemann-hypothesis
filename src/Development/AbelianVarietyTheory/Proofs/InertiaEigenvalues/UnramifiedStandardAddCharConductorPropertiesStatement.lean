module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedStandardAddCharConductorProperties
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

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unramifiedStandardAddChar_conductor_properties : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∃ ψ : AddChar F ℂ, IsStdChar ψ) ∧ ∀ ψ : AddChar F ℂ, IsStdChar ψ → IsLocallyConstant (fun x => ψ x) ∧ (∀ x, ‖ψ x‖ = 1) ∧ (∀ y : F, (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  first | exact @GlobalTheory.StdChar.psi_conductor | exact GlobalTheory.StdChar.psi_conductor | (intros; apply GlobalTheory.StdChar.psi_conductor <;> assumption)
