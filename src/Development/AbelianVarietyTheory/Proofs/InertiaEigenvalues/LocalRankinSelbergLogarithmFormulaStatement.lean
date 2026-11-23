module

public import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Mathlib.Data.Multiset.Functor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormula
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

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW

theorem _root_.GlobalTheory.T.localRankinSelberg_logarithm_formula : (∀ (q : ℕ) (A B : Multiset ℂˣ) (s : ℂ), 1 < q → (∀ α ∈ A, ∀ β ∈ B, ‖(α : ℂ) * (β : ℂ)‖ * (q : ℝ) ^ (-s.re) < 1) → ∃ L : ℂ, HasSum (fun r : ℕ => (A.map fun α => (α : ℂ) ^ (r + 1)).sum * (B.map fun β => (β : ℂ) ^ (r + 1)).sum * (q : ℂ) ^ (-(((r : ℂ) + 1) * s)) / ((r : ℂ) + 1)) L ∧ locL q A B s = Complex.exp L) ∧ (∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∀ x : ℝ, 1 < x → Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ => ‖((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)‖) ∧ HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (Complex.exp (∑' p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ, ((sat σ p.1.1).map fun α => (α : ℂ) ^ (p.2 + 1)).sum * ((sat σ' p.1.1).map fun β => (starRingEnd ℂ (β : ℂ)) ^ (p.2 + 1)).sum * (Ideal.absNorm p.1.1.asIdeal : ℂ) ^ (-(((p.2 : ℂ) + 1) * (x : ℂ))) / ((p.2 : ℂ) + 1)))) := by
  first | (exact @GlobalTheory.JSLog.logRankinSelberg) | (exact GlobalTheory.JSLog.logRankinSelberg) | (intros; apply GlobalTheory.JSLog.logRankinSelberg  <;> assumption)
