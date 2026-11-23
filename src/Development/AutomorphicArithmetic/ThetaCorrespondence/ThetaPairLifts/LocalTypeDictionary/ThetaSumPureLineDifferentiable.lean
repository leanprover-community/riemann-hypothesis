module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSumDifferentiableAlongLine
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
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ThetaLinePureW
theorem hasDerivAt_thetaSum_pure_weight : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' h γ hγ f _ f₁ hD φ hφ hv u
  have H := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP G.M B.ψ X.β (X.β / X.α) om h.base.cm h.base.std h.geo.hM h.weil γ hγ 1 (fun _ => f) (fun _ => f₁)
    (fun _ => φ) (fun _ => ⟨hφ, hv⟩) (fun _ => hD) u
  simpa using H
end GlobalTheory.ThetaLinePureW
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.thetaSum_pure_line_differentiable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ u : Matrix (Fin a) (Fin (a + a')) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))))
      (GlobalTheory.WeilM.thetaSum F (G.M.co.rho B.ψ u (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ))) 0 := by
  first | exact @_root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | exact _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight | (intros; apply _root_.GlobalTheory.ThetaLinePureW.hasDerivAt_thetaSum_pure_weight <;> assumption)
end
