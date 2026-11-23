module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesOneParameterFlow
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

theorem _root_.GlobalTheory.T.center_commutes_one_parameter_flow : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), (∀ (g : GL (Fin a) (Cinf E)) (X : Lie E a), rt E a (infGL E a g) * lie E a X = lie E a (toL (g.val * Matrix.of X * (g⁻¹).val)) * rt E a (infGL E a g)) → ∀ z : Module.End ℂ (Sm E a), z ∈ Zalg E a → (∀ X : Lie E a, z * lie E a X = lie E a X * z) → ∀ (c : ℝ → GL (Fin a) (Cinf E)) (Y : Lie E a), c 0 = 1 → (∀ s, HasDerivAt (fun t => toL (c t).val) (toL ((c s).val * Matrix.of Y)) s) → (∀ s, HasDerivAt (fun t => toL ((c t)⁻¹).val) (toL (-(Matrix.of Y * ((c s)⁻¹).val))) s) → z * rt E a (infGL E a (c 1)) = rt E a (infGL E a (c 1)) * z := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve | exact GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.Flow.zalg_comm_rt_curve <;> assumption)
