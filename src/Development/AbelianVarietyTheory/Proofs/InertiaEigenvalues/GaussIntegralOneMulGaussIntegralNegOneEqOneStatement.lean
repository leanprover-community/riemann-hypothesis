module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOne
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

@[expose] public section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.gaussIntegral_one_mul_gaussIntegral_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ → (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) → gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | exact GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one <;> assumption)
