module

public import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightModule
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem _root_.GlobalTheory.T.exists_highest_weight_module : ∀ {n : ℕ} (κ : Fin n → ℝ), Antitone κ → ∀ s : ℝ, (∀ a, ∃ m : ℤ, κ a - s = m) →
    ∀ w : Equiv.Perm (Fin n),
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : InnerProductSpace ℂ Z) (_ : FiniteDimensional ℂ Z)
      (E : Fin n → Fin n → Module.End ℂ Z) (u a : Z),
      Formalism.REAL.GlRel E ∧ (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) ∧ u ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) E κ u ∧
      (∀ W : Submodule ℂ Z, (∀ x y, ∀ f ∈ W, E x y f ∈ W) → u ∈ W → W = ⊤) ∧ a ≠ 0 ∧
      (∀ x, E (w x) (w x) a = ((κ x : ℝ) : ℂ) • a) ∧ ∀ x y, x < y → E (w x) (w y) a = 0 := by
  exact @GlobalTheory.CompanionTheory.RealCount.Extremal.extremal_module
