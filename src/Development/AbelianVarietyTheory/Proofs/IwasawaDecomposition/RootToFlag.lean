module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

namespace GlobalTheory.GrassTop

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def rootToFlag (H : Host E) (Dw : Datum H) (x : Root Dw.mult) :
    MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : x.1 (H.rt : E) = H.rt0 then
    X (⟨x.1, h⟩, ⟨x.2, by have := x.2.isLt; simp only [Datum.mult, h, if_true] at this; omega⟩)
  else
    -X (⟨conjEmb x.1, GlobalTheory.AllWt.conj_mem h⟩,
      ⟨Dw.p + (Dw.q - 1 - x.2), by have := x.2.isLt; simp only [Datum.mult, h, if_false] at this; omega⟩)

noncomputable def rho (H : Host E) (Dw : Datum H) :
    MvPolynomial (Root Dw.mult) ℝ →ₐ[ℝ] MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  aeval (rootToFlag H Dw)

noncomputable def intGr (H : Host E) (Dw : Datum H) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : ℝ :=
  Formalism.DegreeFormula.degFl (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q)
            (rho H Dw (chernRoots Dw.mult Q * rootDiscr Dw.mult)) /
    ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H))

noncomputable def relIdeal (H : Host E) (Dw : Datum H) : Ideal (MvPolynomial ((E →+* ℂ) × ℕ) ℝ) :=
  Ideal.span ((Set.range fun τ : E →+* ℂ => (X (τ, 0) - 1 : MvPolynomial ((E →+* ℂ) × ℕ) ℝ)) ∪
    {P | ∃ (τ : E →+* ℂ) (k : ℕ), Dw.mult τ < k ∧ P = X (τ, k)} ∪
    {P | ∃ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k ∧
      P = ∑ a ∈ Finset.range (k + 1),
        C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)})

end GlobalTheory.GrassTop
