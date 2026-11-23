module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomFramesChangeStageZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLatticeChangeConstantsAwayUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomStageTransportSameConstantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactorStatement
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
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqTower
theorem theta_tower_bottom_constant_ratio : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  intro _ _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W S _ hN i j A A' WW X B B' WW₁ Y c hX hY hc
  obtain ⟨Y₁, hY₁, hc₁⟩ := GlobalTheory.T.definiteBottom_stage_transport_same_constants W i j X Y hX hY
  obtain ⟨Z₁, v₁, hZ₁, e1, e2, e3, hv₁, hc₂⟩ := GlobalTheory.T.definiteBottom_lattice_change_constants_awayUnit μ₀ hμ W S hN i j X Y₁ hX hY₁
  obtain ⟨Z₂, v₂, hZ₂, f1, f2, f3, f4, f5, f6, hv₂, hc₃⟩ := GlobalTheory.T.definiteBottom_framesChange_stageZero μ₀ hμ W S hN i j X Z₁ hX hZ₁ e1 e2 e3
  obtain ⟨κ, hκ, hX'⟩ := GlobalTheory.T.definiteBottom_tower_constants_differ_by_factor W i j X Z₂ hX hZ₂ f1 f2 f3 f4 f5 f6 _ (hc₃ _ (hc₂ _ (hc₁ c hc)))
  refine ⟨fun t => κ * (v₂ t * v₁ t), ?_, fun t => ?_⟩
  · convert hX' using 2 with t
    ring
  · obtain ⟨h1, ζ₁, u₁, q₁⟩ := hv₁ t
    obtain ⟨h2, ζ₂, u₂, q₂⟩ := hv₂ t
    refine ⟨mul_ne_zero hκ (mul_ne_zero h2 h1), ζ₂ * ζ₁, u₂.mul u₁, ?_⟩
    show κ * (v₂ t * v₁ t) = _ * (κ * (v₂ μ₀ * v₁ μ₀))
    rw [q₁, q₂, map_mul]
    ring
end GlobalTheory.SqTower
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

theorem _root_.GlobalTheory.T.witt_tower_constant_ratio_eq_bottom : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW) (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c : T → ℂ),
      IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y → Y.IsConst W.ψ W.θ c → ∃ v : T → ℂ,
        X.IsConst W.ψ W.θ (fun t => v t * c t) ∧
        ∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀ := by
  exact @_root_.GlobalTheory.SqTower.theta_tower_bottom_constant_ratio
end
