module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSymplecticLieEqExpOneParamStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanLineSpannedByWeilVector
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MetaplecticScalarDerivativeNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
theorem GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∀ f : SInf F (Fin n × Fin d), ∃ (c : ℝ → SInf F (Fin n × Fin d)) (c' : SInf F (Fin n × Fin d)),
      c 0 = f ∧ Filter.Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (nhdsWithin 0 {0}ᶜ) (nhds c') ∧
      ∀ t : ℝ, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑(c t)) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hψ hw γ hγ f
  obtain ⟨l, _, _, Φ, g, T, hgc, hg0, hgm, hgs, hT0, hTm, hTi, hTu, hTc, hTa⟩ :=
    _root_.GlobalTheory.T.archimedean_line_spanned_by_weil_vector hP M ψ χX χW om hcm hψ hw γ hγ
  obtain ⟨Z, hZ, hgZ⟩ := GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam l g hgc hg0 hgm hgs
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq hP l Z hZ T hT0 hTm
    (fun t w h h₁ e => by rw [← hgZ t]; exact hTi t w h h₁ e) hTu hTc
  refine ⟨fun t => Φ.symm (T t (Φ f)), Φ.symm (a • Φ f + GlobalTheory.RealWeil.quad Z (Φ f)), ?_, ?_, fun t => hTa t f⟩
  · simp [hT0]
  · have h := (Φ.symm.continuous.tendsto _).comp (ha (Φ f))
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, ← Complex.coe_smul, map_smul, map_sub, ContinuousLinearEquiv.symm_apply_apply]
end
