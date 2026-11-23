module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MinorOrderedEntries
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpan
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, FiniteDimensional ℂ (H τ)] (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (lamH : ι → Fin n → ℝ) (lam : ι → ℕ → ℤ), (∀ τ, StrictAnti (lamH τ)) → (∀ τ, Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) (σ τ)) → (∀ τ, Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) (σ τ) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) ⊤) → (∀ τ (i : Fin n), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) (Fin.rev i)) → ∃ Φ : Module.Dual ℂ (weylSub n lam) ≃ₗ[ℂ] ⨂[ℂ] τ, H τ, ∀ (u : UG ι n) (φ : Module.Dual ℂ (weylSub n lam)), Φ ((weylRep n lam).dual u φ) = PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) (Φ φ) := by
  first | exact @GlobalTheory.DualWeylTensor.main | exact GlobalTheory.DualWeylTensor.main | (intros; apply GlobalTheory.DualWeylTensor.main <;> assumption)
