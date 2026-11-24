module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitarySignatureStabiliserCosetCutoff
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
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct


theorem _root_.GlobalTheory.T.exists_unitarySignatureStabiliserCosetCutoff : ∀ (c : CDHaar) (P Q P' Q' : ℕ) (x₀ : ActionCoordinates.Wsp P Q), ActionCoordinates.qf x₀ ≠ 0 → ∀ (j : ActionCoordinates.Wsp P' Q' →ₗ[ℂ] ActionCoordinates.Wsp P Q) (ι : UpqT P' Q' → UpqT P Q), ActionCoordinates.IsPerpFrame x₀ j ι → Set.range ι = {g | ActionCoordinates.act g x₀ = x₀} → ∃ u : UpqT P Q → ℝ≥0∞, Measurable u ∧ ∀ g, Measurable (fun h => u (ι h * g)) ∧ ∫⁻ h, u (ι h * g) ∂(c.cd P' Q') = 1 := by
  first | exact @GlobalTheory.StabiliserCutoff.exists_cutoff | exact GlobalTheory.StabiliserCutoff.exists_cutoff | (intros; apply GlobalTheory.StabiliserCutoff.exists_cutoff <;> assumption)
