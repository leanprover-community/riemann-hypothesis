module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqAmpJAndBesselEqDoubleIntegral
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

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.amplitude_eq_ampJ_and_bessel_eq_doubleIntegral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] , (∀ (μG : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq), IsHaarOn (GG k r) μG → ∀ γ ∈ GG k r, OO μG Φ Φ' γ = ampJ μG 1 Φ Φ' γ) ∧ ∀ (σ : Mat k r → (H →L[ℂ] H)) (z z' : Fin (2 * r + k + 1) → ℂ) (c₀ : ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μW μW' μN : Measure (Mt k r)) (x y : H) (ξ : Wp) (ξ' : Wq), inWb k r z → 0 < Tz k r z → inWb k r z' → 0 < Tz k r z' → IsURepOn (GG k r) σ → IsURepOn (UWset k r z) π → IsURepOn (UWset k r z') π' → IsHaarOn (UWset k r z) μW → IsHaarOn (UWset k r z') μW' → IsHaarOn (Nset k r) μN → ∀ γ ∈ GG k r, besselJ k r z z' c₀ π π' μW μN μW' (fun g => coef σ x y g • rk1 ξ ξ') γ = Iint (psi k r z c₀) (psi k r z' c₀) π π' ((μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) ((μW'.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2) σ x y ξ ξ' γ := by
  first | exact @GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint | exact GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint | (intros; apply GlobalTheory.SgInf.AmpJ.oo_eq_ampJ_and_besselJ_eq_Iint <;> assumption)
