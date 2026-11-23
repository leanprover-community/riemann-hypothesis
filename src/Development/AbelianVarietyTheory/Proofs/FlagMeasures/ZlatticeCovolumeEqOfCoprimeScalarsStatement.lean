module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ZlatticeCovolumeEqOfCoprimeScalars
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.zlattice_covolume_eq_of_coprime_scalars : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (A B : Submodule ℤ (ι → κ → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A] [DiscreteTopology B] [IsZLattice ℝ B], (∀ p : ℕ, p.Prime → ∃ (d : ι → ℝ) (N : ℕ), ¬ p ∣ N ∧ ∏ v, d v ^ 2 = N ∧ (∀ y ∈ A, (fun v i => d v * y v i) ∈ B) ∧ ∀ y ∈ B, (fun v i => d v * y v i) ∈ A) → ZLattice.covolume A volume = ZLattice.covolume B volume := by
  first | exact @GlobalTheory.CovScal.covolume_eq_of_scalars | exact GlobalTheory.CovScal.covolume_eq_of_scalars | (intros; apply GlobalTheory.CovScal.covolume_eq_of_scalars <;> assumption)
