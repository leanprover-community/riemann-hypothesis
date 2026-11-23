module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFramesDoublingPolynomialExists
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.TopDict
open Matrix
theorem theta_parameter_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j X hG hX A A₁ AV AV₁ hA hA₁ hAV hAV₁
  exact dict_frames X _ _ _ _ _ _ hX.2.2.2.2.2.2.2 A A₁ (frSum AV AV₁)
    (hG.2.2.2.1.trans (funext fun τ => (hA τ).2.symm)) (hG.2.2.2.2.1.trans (funext fun τ => (hA₁ τ).2.symm))
    (hG.2.2.2.2.2 AV AV₁ hAV hAV₁)
end GlobalTheory.TopDict
end
end

section
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.theta_parameter_dictionary_bijective : _root_.GlobalTheory.FunPr.ThetaLocalInputs →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (X : TriG G i j), TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X →
    ∀ (A : Fr (G.V (.grid (i + 1) (j + 1)))) (A₁ : Fr (G.V (.grid i j))) (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ A → IsGridFr W _ A₁ → IsGridFr W _ AV → IsGridFr W _ AV₁ →
    ∃ (σ : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid (i + 1) (j + 1))).rank)
      (σ' : PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank ≃ₗ[ℂ] PolF D (GlobalTheory.Doubling.hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank (G.V (.grid i j)).rank), ∀ t : T,
      IsFinF W.ψ W.θ true A (frSum AV AV₁) (X.f t) ∧ IsFinF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) ∧
      (∀ P g h, X.ker W.ψ W.θ t P h g = thetaKO (X.ω t) g h (fockF W.ψ W.θ true A (frSum AV AV₁) (X.f t) (σ P))) ∧
      ∀ P g h, X.ker' W.ψ W.θ t P h g = thetaKO (X.ω' t) g h (fockF W.ψ W.θ false A₁ (frSum AV AV₁) (X.f' t) (σ' P)) := by
  first | exact @_root_.GlobalTheory.TopDict.theta_parameter_dictionary | exact _root_.GlobalTheory.TopDict.theta_parameter_dictionary | (intros; apply _root_.GlobalTheory.TopDict.theta_parameter_dictionary <;> assumption)
end
