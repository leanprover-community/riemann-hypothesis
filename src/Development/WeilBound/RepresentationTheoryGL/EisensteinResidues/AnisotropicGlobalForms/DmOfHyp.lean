module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingBasicIdentityUnfoldingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinContinuationAndPoles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSphericalModerateGrowthRealPointStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
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

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled

def DM : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      (EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k) ∧ True ∧
      ∀ θ : InfFam D, IsInfFam θ → V.SigOK → ∀ A : CptF V, GlobalTheory.Cusp.IsCartanFrame V A →
        ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ ∈ GlobalTheory.Cusp.A0 θ V A, ∀ f₂ ∈ GlobalTheory.Cusp.A0 θ V A,
          (∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂) ∧
          ZetaContinues V μ m (flat V a φ s₁) f₁ f₂

theorem dm_of_two : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → True → DM := by
  intro hC hS _ D V hV a ha hI μ b hμ hb s₁ φ hφ
  have h1 := hS D V hV a ha hI μ b hμ hb s₁ φ hφ
  refine ⟨h1, trivial, fun θ hθ _ A _ m hm f₁ h₁ f₂ h₂ => ?_⟩
  have r₁ := GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2
  have r₂ := GlobalTheory.Grow.rapidDec_of_cuspForm hC hθ (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.1 (GlobalTheory.Cusp.mem_cuspForms.1 h₂).1.2
  have hB : ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → BasicIdentity V μ m (flat V a φ s₁ s) f₁ f₂ := fun s hs =>
    GlobalTheory.T.doubling_basicIdentity_unfolding D V a ha μ hμ s hs _ (flat_mem hI hφ s) (GlobalTheory.T.siegelEisenstein_spherical_moderateGrowth_real_point hS D V hV a ha hI s.re hs) m hm f₁ f₂ r₁ r₂
      (GlobalTheory.Cusp.mem_cuspForms.1 h₁).1.2
  exact ⟨hB, zetaContinues_of_eisRegularAt hμ hm h1.1 h1.1.1.analyticOnNhd_flat h1.2 r₁ r₂
    ⟨h1.1.1, fun s hs => (hB s hs).1⟩⟩

end ResidueKilled
