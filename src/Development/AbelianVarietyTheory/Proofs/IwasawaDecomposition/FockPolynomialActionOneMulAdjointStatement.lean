module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialActionOneMulAdjoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fockPolynomialAction_one_mul_adjoint : ∀ (D : D7) (m n : ℕ) (ε : D.what₂.Tau → Fin m → Bool) (x₁ x₂ x₃ : D.what₂.Tau → ℤ), fact (n := n) ε x₁ x₂ x₃ 1 1 = 1 ∧ (∀ (k k' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u u' : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, k' τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → (∀ τ, IsUnit (u' τ)) → fact ε x₁ x₂ x₃ (k * k') (u * u') = fact ε x₁ x₂ x₃ k u * fact ε x₁ x₂ x₃ k' u') ∧ ∀ (k : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (u : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ), (∀ τ, k τ ∈ GlobalTheory.Dec.KC (ε τ)) → (∀ τ, IsUnit (u τ)) → ∀ F F' : PolF D m n, fockL (fact ε x₁ x₂ x₃ k u F) F' = fockL F (fact ε x₁ x₂ x₃ (fun τ => (k τ)ᴴ) (fun τ => (u τ)ᴴ) F') := by
  first | exact @GlobalTheory.JointHarm.fact_one_mul_adj | exact GlobalTheory.JointHarm.fact_one_mul_adj | (intros; apply GlobalTheory.JointHarm.fact_one_mul_adj <;> assumption)
