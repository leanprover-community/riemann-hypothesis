module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivation
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

@[expose] public section

open Matrix
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem GlobalTheory.T.exists_highest_weight_hermitian_derivation :
    ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν →
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L)
      (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L))
      (K : Fin n → Fin n → Module.End ℂ L) (v : L),
      Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧
      IsDerivK σ K ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
      (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ),
        k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ L (σ k) = weylChar ν z :=
  @GlobalTheory.CompanionTheory.RmModel.rmModel
