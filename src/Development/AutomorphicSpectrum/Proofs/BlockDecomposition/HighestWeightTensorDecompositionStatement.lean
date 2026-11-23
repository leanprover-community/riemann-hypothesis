module

public import Formalism.RealPlaceAnalysis.StatementA
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightTensorDecomposition
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

theorem _root_.GlobalTheory.T.highest_weight_tensor_decomposition : ∀ {n : ℕ} (H V : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (D : Fin n → Fin n → Module.End ℂ H) (D' : Fin n → Fin n → Module.End ℂ V) (μ : Fin n → ℝ), Formalism.REAL.GlRel D → Formalism.REAL.GlRel D' → (∀ a b (x y : H), ⟪D a b x, y⟫_ℂ = ⟪x, D b a y⟫_ℂ) → (∀ a b (x y : V), ⟪D' a b x, y⟫_ℂ = ⟪x, D' b a y⟫_ℂ) → ∀ Hs : Submodule ℂ H, (∀ x ∈ Hs, Formalism.REAL.KHighest (fun _ => true) D μ x) → ∀ f : Hs →ₗ[ℂ] V, (∀ x, Formalism.REAL.KHighest (fun _ => true) D' μ (f x)) → ∃ T : H →ₗ[ℂ] V, (∀ x : Hs, T x = f x) ∧ ∀ a b w, T (D a b w) = D' a b (T w) := by
  exact @GlobalTheory.CompanionTheory.RealCount.ExtHw.kmap_extend
