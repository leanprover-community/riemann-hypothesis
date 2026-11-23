module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInj

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  intro F _ _ ψ hψ κ _ Φ hΦ h
  have hn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
  let ι : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  have hΦx : (fun z => Φ (z + x)) ∈ schA F κ := GlobalTheory.SchwartzTranslate.schA_translate F x hΦ
  have hc : Summable fun ξ => ‖Φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦx using 1
  have key := GlobalTheory.SchrodingerUniq.coeff_zero_eq_zero
    (χ := fun (y : κ → AF F) (ξ : κ → F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => Φ (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap F (AF F) (ξ i) * (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have e2 : ∑' ξ : κ → F, Φ (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → F, ψ (ι ξ ⬝ᵥ y) * b * Φ (ι ξ + x) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; field_simp
    rw [e2, h', mul_zero]

end GlobalTheory.ThetaInj
