module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w (n := n) → k₂ ∈ KGL w (n := n) → ∃ κ ∈ KGL w (n := (n + n)), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  first | exact @GlobalTheory.GraphShear.graph_shear | exact GlobalTheory.GraphShear.graph_shear | (intros; apply GlobalTheory.GraphShear.graph_shear <;> assumption)
