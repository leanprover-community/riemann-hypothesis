module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselEmbeddingEqLastGLRootExchangeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawWeilBiActionCommutes
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecondStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TriStep.valK_gl₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (rTrans (Q.gl₂ (embX (Q.c + 1) g)) f) = ((nabs Q.k (Matrix.GeneralLinearGroup.det g) ^ ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ h₁ h₂ φ hφ Λ hΛ g Ξ₁ Ξ₂ Ξ₂' hΞ hC f hf
  obtain ⟨a₀, ha, hloc⟩ := (GlobalTheory.T.exists_besselEmbedding_eq_lastGL_rootExchange) D ψ σ S Q g
  have hop := (GlobalTheory.T.weilOperator_lastDefiniteLocal_biModel_second) D ψ σ S Q c₁ c₂ h₂ Λ hΛ g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ
  have hf0 : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, GlobalTheory.TriStep.rTrans_one] at this
  have hF := GlobalTheory.SeeSawLastValue.contAut_biLift (GlobalTheory.SeeSaw.biAct_all D) S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ hC
  have hB3 := ((GlobalTheory.SeeSaw.biAct_all D) ψ _ _ _ _ _ _ _ S.oma S.omb S.weila S.weilb _ hC).2.2.1
  have hshift : biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂'))) =
      rTrans a₀ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)))) := by
    funext h
    simp only [biLift, rTrans]
    congr 1; funext h₁; congr 1; funext h₀; congr 1
    have e : ((h₁, h * a₀) : GA D S.J.W₀ × GA D S.B'.A) = (h₁, h) * (1, a₀) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    refine congrArg (fun X => S.omb (h₁, h) X 0) ?_
    funext v
    rw [hB3]
    refine congrArg (fun X => S.oma (h₀, h₁) X 0) ?_
    funext u
    rw [hop u]
  have hc : Q.c + 1 = 2 * σ + 1 := Q.F.bes'.1
  have hexp : ((((Q.c + 1 : ℕ) : ℝ) + 1) / 2 - ((σ + 1 : ℕ) : ℝ)) = 0 := by
    rw [hc]; push_cast; ring
  rw [hexp, Real.rpow_zero, Complex.ofReal_one, one_mul]
  unfold GlobalTheory.TriStep.valK
  rw [hshift, ← ha]
  exact GlobalTheory.Core.Mi.per_rTrans D ψ σ S.B' _ f a₀ hψ hF hf0
