module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleIntegralVanishing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageThetaDictionaryExistsStatement
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralKernelLieAlgebraStable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaSmallRankStageHolds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaStageLiftExists
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.StageKer
end GlobalTheory.StageKer
theorem GlobalTheory.StageKer.theta_stage_kernel_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.SqTop.Model.gBig_and GlobalTheory.T.towerStage_thetaDictionary_exists (_root_.GlobalTheory.T.theta_stage_liftable hP hK hL)) (_root_.GlobalTheory.T.theta_small_rank_stage_holds hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hLc G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨⟨h1, h3⟩, h4⟩ := h C hC D large₂ a b r T Lc μ hLc G
  obtain ⟨FA, FA', FW, ea, eb, hD⟩ := h1 W S hW hN i j p q A A' WW X hX
  obtain ⟨lam, s, hlam, hs⟩ := h3 W S hW hN i j p q A A' WW X hX
  obtain ⟨P0, hc0, hne0⟩ := h4 W S hW hN i j p q A A' WW X hX
  obtain ⟨Pr, qP, hq⟩ := _root_.GlobalTheory.T.thetaIntegral_factors_through_kType hP hK hL D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW ea eb
  have hIs := hX.2.2.2.2.2.2.2
  have key : ∀ t P, X.I W.ψ W.θ t P = 0 ↔ qP P = 0 := by
    intro t
    obtain ⟨hTr, hInf, hf, -, hk, -⟩ := hD t
    obtain ⟨Pf, y, J, hJ, hI⟩ := hq _ _ hTr hInf X.m X.fd hIs.meas (X.ω t) (hIs.weil t) (X.f t) hf
    have eI : ∀ P, X.I W.ψ W.θ t P = J (qP P ⊗ₜ y) := fun P => by
      rw [← hI P]; funext h; simp only [GlobalTheory.SquareComm.thetaInt, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Tri.I, hk]
    have hne : X.I W.ψ W.θ t (s P0) ≠ 0 := by
      rw [hs t P0 (hc0 t)]; exact smul_ne_zero (hlam t) (hne0 t)
    have hy : y ≠ 0 := by
      rintro rfl; apply hne; rw [eI, TensorProduct.tmul_zero, map_zero]
    have hJi : Function.Injective J := hJ.resolve_left (by
      intro hJ0; apply hne; rw [eI, hJ0]; rfl)
    intro P
    rw [eI, map_eq_zero_iff J hJi]
    constructor
    · intro h0; by_contra hq0; exact GlobalTheory.StageKer.tmul_ne_zero_of_ne hq0 hy h0
    · intro h0; rw [h0, TensorProduct.zero_tmul]
  intro t t' P h0
  exact (key t' P).2 ((key t P).1 h0)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.theta_stage_kernel_characterization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t t' P, X.I W.ψ W.θ t P = 0 → X.I W.ψ W.θ t' P = 0 := by
  exact @_root_.GlobalTheory.StageKer.theta_stage_kernel_eq
end
