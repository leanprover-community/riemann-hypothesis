module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTangentBorelSectionQuadric
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

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.exists_tangent_borelSection_quadric : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), ∃ σ : Sp P Q → UpqT P Q, IsSection (sg (e none)) (baseVec e) σ ∧ ∀ y : Sp P Q, qf y = sg (e none) → y (e none) ≠ -1 → (∀ b, ‖UpqT.mat (σ y) (e none) (e (some b))‖ = ‖y (e (some b))‖) ∧ ∀ a b, ‖(UpqT.mat (σ y) - 1) (e (some a)) (e (some b))‖ = ‖y (e (some a))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖ := by
  first | exact @GlobalTheory.TangentSection.exists_tangent_section | exact GlobalTheory.TangentSection.exists_tangent_section | (intros; apply GlobalTheory.TangentSection.exists_tangent_section <;> assumption)
