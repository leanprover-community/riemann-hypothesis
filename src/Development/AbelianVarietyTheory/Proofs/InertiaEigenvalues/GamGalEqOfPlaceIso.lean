module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.FunExt GlobalTheory.Published

noncomputable section

namespace GlobalTheory.RSGam.Transport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'}

theorem wdRel_mk (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : WDRep h V) (b' : WDRep h' V)
    (hN : b.N = b'.N) (hρ : ∀ σ, b'.ρ (c σ) = b.ρ σ) : WDRel φ (WD.mk b) (WD.mk b') := by
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
  refine ⟨_, b.transport e, b'.transport e, WD.sound (b.iso_transport e).symm,
    WD.sound (b'.iso_transport e).symm, ?_, fun σ σ' hσ => ?_⟩
  · show e.conjAlgEquiv ℂ b.N = e.conjAlgEquiv ℂ b'.N
    rw [hN]
  · show e.conjAlgEquiv ℂ (b.ρ σ) = e.conjAlgEquiv ℂ (b'.ρ σ')
    rw [← (hcr σ σ').1 hσ, hρ]

theorem wdRel_lpUnr (c : Weil h ≃* Weil h') (hcr : ∀ σ σ', WeilRel φ σ σ' ↔ c σ = σ')
    (hdeg : ∀ σ, deg (c σ) = deg σ) (m : Multiset ℂ) :
    WDRel φ (WD.lpUnr (h := h) m) (WD.lpUnr (h := h') m) := by
  classical
  unfold WD.lpUnr
  refine wdRel_mk c hcr _ _ rfl fun σ => ?_
  rw [WDRep.diag_ρ, WDRep.diag_ρ, hdeg]

end GlobalTheory.RSGam.Transport

end
