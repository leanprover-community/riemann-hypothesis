module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianTermMeasurableAndStabilizerInvariant
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.gaussianTerm_measurable_and_stabilizer_invariant : ∀ (I : AutInst) (x : Fin I.n → I.E), IsOpen {h : I.Gf | x ∈ lamX I (1, h)} ∧ (∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) => ENNReal.ofReal (gauss ((uMat g)⁻¹ *ᵥ infVec I v x))) ∧ (∀ h g : I.Gf, I.fmat h *ᵥ afVec I x = afVec I x → (x ∈ lamX I (1, h * g) ↔ x ∈ lamX I (1, g))) ∧ (∀ g : I.Gf, ∀ k ∈ I.Kset, x ∈ lamX I (1, g * k) ↔ x ∈ lamX I (1, g)) ∧ ∀ v (h g : Formalism.REAL.UJ (I.ε v)), uMat h *ᵥ infVec I v x = infVec I v x → (uMat (h * g))⁻¹ *ᵥ infVec I v x = (uMat g)⁻¹ *ᵥ infVec I v x := by
  first | exact @GlobalTheory.StabUnfold.gaussAt_meas_inv | exact GlobalTheory.StabUnfold.gaussAt_meas_inv | (intros; apply GlobalTheory.StabUnfold.gaussAt_meas_inv <;> assumption)
