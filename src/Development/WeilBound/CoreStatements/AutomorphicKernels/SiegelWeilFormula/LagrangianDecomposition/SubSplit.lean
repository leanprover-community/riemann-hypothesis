module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.IsSingTest
import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def OpBox : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F)
    (dd : Darboux B (κ' ⊕ κ'')) (G : Type) [Group G] (act : G → W → W)
    (om : G →* Module.End ℂ ((κ' ⊕ κ'' → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    (∀ u v : κ'' → AF F, ∃ w, dd.e w = (Sum.elim (0 : κ' → AF F) u, Sum.elim (0 : κ' → AF F) v)) →
    ∀ x : G, (∀ w, (dd.e w).1 ∘ Sum.inl = 0 → (dd.e w).2 ∘ Sum.inl = 0 → act x w = w) →
    ∀ φ₀ ∈ schA F κ'', φ₀ 0 = 1 →
      (∀ Ψ ∈ schA F (κ' ⊕ κ''), slice0 κ' κ'' (om x Ψ) = slice0 κ' κ'' (om x (boxFun (slice0 κ' κ'' Ψ) φ₀))) ∧
      ∀ φ' ∈ schA F κ', ∀ φ'' ∈ schA F κ'',
        om x (boxFun φ' φ'') = boxFun (slice0 κ' κ'' (om x (boxFun φ' φ₀))) φ''

def SubSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (W W' : Type) [AddCommGroup W] [Module (AF F) W] [AddCommGroup W']
    [Module (AF F) W'] (B : W → W → AF F) (B' : W' → W' → AF F) (dd : Darboux B (κ' ⊕ κ'')) (dd' : Darboux B' κ')
    (emb : W' → W), (∀ w', dd.e (emb w') = (Sum.elim (dd'.e w').1 0, Sum.elim (dd'.e w').2 0)) →
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (act : G → W → W)
    (act' : G' → W' → W') (j : G' →* G), Continuous j → (∀ g w', act (j g) (emb w') = emb (act' g w')) →
  ∀ (om : G →* Module.End ℂ ((κ' ⊕ κ'' → AF F) → ℂ)) (om' : G' →* Module.End ℂ ((κ' → AF F) → ℂ)),
    IsUSplitting (adeleClass F) ψ dd act om →
  ∀ φ₀ ∈ schA F κ'', φ₀ 0 = 1 →
    (∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
      ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ 0 ∧ ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ ⊤) →
    (∀ g, ∃ φ₁ ∈ schA F κ'', φ₁ 0 = 1 ∧
      (∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
        ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ'' = ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'') ∧
      ∀ φ' ∈ schA F κ', om (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₁) →
    IsUSplitting (adeleClass F) ψ dd' act' om'

end PositivityTheory.SiegelWeilFormula.Ald

end
