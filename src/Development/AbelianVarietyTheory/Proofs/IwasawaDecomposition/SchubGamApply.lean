module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def flagRoot {H : Host E} (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_mem Dw h; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have h1 : (x.2 : ℕ) < Dw.mult x.1 := x.2.2; have h2 := GlobalTheory.PointChern.mult_of_not_mem Dw h; omega⟩)

def flagMap {H : Host E} (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (flagRoot Dw)

def flagLin (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) : MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ Formalism.DegreeFormula.dimFl ι N) • ∑ σ : ι → Equiv.Perm (Fin N),
    (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) • lcoeff ℝ (Formalism.DegreeFormula.permExp σ)

theorem flagLin_apply (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (P : MvPolynomial (ι × Fin N) ℝ) :
    flagLin ι N P = Formalism.DegreeFormula.degFl ι N P := by
  simp [flagLin, Formalism.DegreeFormula.degFl, LinearMap.sum_apply, smul_eq_mul, Finset.mul_sum]

def schubGam {H : Host E} (Dw : Datum H) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ :=
  flagLin (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) ∘ₗ (flagMap Dw).toLinearMap ∘ₗ
    LinearMap.mulRight ℝ (fibrePoint Dw.mult) ∘ₗ (chernRoots Dw.mult).toLinearMap

theorem schubGam_apply {H : Host E} (Dw : Datum H) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :
    schubGam Dw P = Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
      (flagMap Dw (chernRoots Dw.mult P * fibrePoint Dw.mult)) := by
  simp [schubGam, flagLin_apply]

def admitted (H : Host E) (Dw : Datum H) (Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ) : Prop :=
  (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P, Θ (GlobalTheory.PointChern.relPoly τ k * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Θ ((X (τ, 0) - 1) * P) = 0) ∧
  (∀ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, Θ (X (τ, k) * P) = 0) ∧
  (∀ d : (E →+* ℂ) × ℕ →₀ ℕ, (d.sum fun x i => x.2 * i) ≠ Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) →
    Θ (monomial d 1) = 0)

end GlobalTheory.Schubert
