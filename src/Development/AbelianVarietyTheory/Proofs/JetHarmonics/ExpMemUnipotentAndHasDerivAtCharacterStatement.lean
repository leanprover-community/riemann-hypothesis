module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exp_mem_unipotent_and_hasDerivAt_character : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  first | exact @GlobalTheory.UnipotentExp.exp_mem_and_deriv | exact GlobalTheory.UnipotentExp.exp_mem_and_deriv | (intros; apply GlobalTheory.UnipotentExp.exp_mem_and_deriv <;> assumption)
