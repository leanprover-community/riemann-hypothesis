module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConjStableLatticeRealImagCovolumeLe
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.conjStable_lattice_real_imag_covolume_le : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (L : Submodule ℤ (ι → κ → ℂ)) [DiscreteTopology L] [IsZLattice ℝ L], (∀ z ∈ L, (fun v i => starRingEnd ℂ (z v i)) ∈ L) → ∀ A B : Submodule ℤ (ι → κ → ℝ), (∀ y, y ∈ A ↔ (fun v i => (y v i : ℂ)) ∈ L) → (∀ y, y ∈ B ↔ (fun v i => Complex.I * (y v i : ℂ)) ∈ L) → (∃ _ : DiscreteTopology A, IsZLattice ℝ A) ∧ (∃ _ : DiscreteTopology B, IsZLattice ℝ B) ∧ ZLattice.covolume A volume * ZLattice.covolume B volume ≤ 2 ^ (Fintype.card ι * Fintype.card κ) * ZLattice.covolume L volume := by
  first | exact @GlobalTheory.ReImLattice.real_imag_covolume_le | exact GlobalTheory.ReImLattice.real_imag_covolume_le | (intros; apply GlobalTheory.ReImLattice.real_imag_covolume_le <;> assumption)
