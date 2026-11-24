module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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

open MvPolynomial Matrix NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder

namespace GlobalTheory.PointChern

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def coordOf {H : Host E} {Dw : Datum H} {n : ℕ} (e : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ :=
  fun τ i j => w (e.symm (τ, i, j))

def InDom {H : Host E} {Dw : Datum H} (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) : Prop :=
  ∀ τ, (1 - (z τ)ᴴ * z τ).PosDef

theorem mult_of_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : τ (H.rt : E) = H.rt0) : Dw.mult τ = Dw.p := by
  simp [Datum.mult, h]

theorem mult_of_not_mem {H : Host E} (Dw : Datum H) {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    Dw.mult τ = Dw.q := by
  simp [Datum.mult, h]


open Classical in
def modelGram (H : Host E) (Dw : Datum H) (z : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.q) ℂ) :
    GlobalTheory.FlagBundle.Mat Dw.mult ℂ := fun τ =>
  if h : τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
      (1 - (z ⟨τ, h⟩).map (starRingEnd ℂ) * (z ⟨τ, h⟩)ᵀ)⁻¹
  else if h' : conjEmb τ (H.rt : E) = H.rt0 then
    reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
      (1 - (z ⟨conjEmb τ, h'⟩)ᴴ * z ⟨conjEmb τ, h'⟩)⁻¹
  else 1

def relPoly {H : Host E} (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ :=
  ∑ a ∈ Finset.range (k + 1), C ((-1 : ℝ) ^ (k - a)) * X (τ.1, a) * X (conjEmb τ.1, k - a)

end GlobalTheory.PointChern
