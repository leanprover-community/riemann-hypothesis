module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepresentationUnitaryMulContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SecondCountableFiniteAdelicUnitaryPointsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_weakIntegral_of_stronglyContinuous {X H : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (μ : Measure X) (R : X → (H →L[ℂ] H)) (hn : ∀ x F, ‖R x F‖ = ‖F‖)
    (hc : ∀ F, Continuous fun x => R x F) (φ : X → ℂ) (hφ : Integrable φ μ) :
    ∃ T : H →L[ℂ] H, ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, φ g * ⟪x, R g y⟫_ℂ ∂μ := by
  have hint : ∀ y : H, Integrable (fun g => φ g • R g y) μ := fun y =>
    (hφ.norm.mul_const ‖y‖).mono' (hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [norm_smul, hn])
  let Tl : H →ₗ[ℂ] H :=
    { toFun := fun y => ∫ g, φ g • R g y ∂μ
      map_add' := fun y z => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (hint y) (hint z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        ext g
        rw [smul_comm] }
  refine ⟨Tl.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun x y => ?_⟩
  · calc ‖Tl y‖ = ‖∫ g, φ g • R g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • R g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by
        congr 1
        ext g
        rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · show ⟪x, ∫ g, φ g • R g y ∂μ⟫_ℂ = _
    rw [← integral_inner (hint y)]
    congr 1
    ext g
    rw [inner_smul_right]

theorem AutInst_exists_isRConvF_and_isRConv : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R → (∀ e : I.Gf → ℂ, Integrable e μf → ∃ T, I.IsRConvF μf fund R e T) ∧ ∀ φ : I.GA → ℂ, Integrable φ (I.muA μf) → ∃ T, I.IsRConv μf fund R φ T := by
  intro I μf _ _ fund hfund R hR
  obtain ⟨-, -, hn, hc⟩ := GlobalTheory.T.rightRegularRepresentation_unitary_mul_continuous I μf fund hfund R hR
  haveI := GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints I
  refine ⟨fun e he => ?_, fun φ hφ => ?_⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous μf (fun g => R (1, g))
      (fun g F => hn _ F) (fun F => (hc F).comp (by fun_prop)) e he
    exact ⟨T, he, hT⟩
  · obtain ⟨T, hT⟩ := exists_weakIntegral_of_stronglyContinuous (I.muA μf) R hn hc φ hφ
    exact ⟨T, hφ, hT⟩

end GlobalTheory
