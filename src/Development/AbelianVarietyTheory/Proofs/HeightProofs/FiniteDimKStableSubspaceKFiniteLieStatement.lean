module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
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
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finiteDim_kStable_subspace_kFinite_lie : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → (∀ S : Submodule ℂ R.U.H, FiniteDimensional ℂ S → IsKStableOn ε σ S → S ≤ LinearMap.range R.ι) ∧ ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → IsKStableOn ε σ (W.map R.ι) → KStable R.HK.act W := by
  first | exact @GlobalTheory.RealPar.KStabLie.kstable_lie | exact GlobalTheory.RealPar.KStabLie.kstable_lie | (intros; apply GlobalTheory.RealPar.KStabLie.kstable_lie <;> assumption)
