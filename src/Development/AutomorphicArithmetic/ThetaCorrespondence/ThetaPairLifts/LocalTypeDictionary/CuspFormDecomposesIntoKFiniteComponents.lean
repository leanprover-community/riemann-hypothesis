module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlacesStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilRepresentationPlaceDecomposition
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open Classical in
theorem GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ hθ hP N ψ hψ U hU hlev hK μ 𝓕 hμ h𝓕
  choose W i1 i2 i3 ρ hρc hρ using hK
  letI := i1; letI := i2; letI := i3
  obtain ⟨n, T₀, u, hv, hk, hl, he⟩ := GlobalTheory.T.kFiniteDecomposition_assemble_realPlaces D θ N (GlobalTheory.KFinDecomp.Cls θ N U)
    (fun τ f => GlobalTheory.Published.AutFin.HasTypeAt θ N.V τ (N.M.ε τ) (N.M.fr τ) (ρ τ) f)
    (fun f hf => hf.1.1.cont) (_root_.GlobalTheory.T.weil_representation_place_decomposition D θ hθ hP N U W ρ hρc) ψ ⟨hψ, hlev⟩ hρ
  refine ⟨n, T₀, u, fun j => ?_, he⟩
  have hc := fun v => (hv j v).1
  refine ⟨fun v => (hc v).1.toIsAutFun, fun v => (hc v).1.smooth, fun v => (hc v).2.1,
    fun v => GlobalTheory.CuspDecay.memLp_two_of_cuspBounded hP.cuspBounded hθ (hc v).1.toIsAutFun (hc v).1.smooth
      (hc v).1.growth (hc v).2.1 μ 𝓕 hμ h𝓕,
    fun v => unifModGrowth_of_isAutFunSm hθ (hc v).1, fun v k hk g => ?_, hk j, hl j⟩
  rw [Pi.one_apply, one_mul]
  exact (hv j v).2 k hk.1 hk.2 g
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

theorem _root_.GlobalTheory.T.cuspForm_decomposes_into_kFinite_components : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (U : Subgroup (GA D N.V)), IsOpen (U : Set (GA D N.V)) → (∀ k ∈ U, k ∈ GfC N.V → ∀ g, ψ (g * k) = ψ g) → (∀ τ, GlobalTheory.CuspKFin.KFinAt θ N τ ψ) → ∀ (μ : Measure (GA D N.V)) (𝓕 : Set (GA D N.V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ N.V) 𝓕 μ → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ N.M {k | k ∈ U ∧ k ∈ GfC N.V} 1 μ 𝓕 (T₀ j)) ∧ ψ = ∑ j, T₀ j (u j) := by
  first | exact @_root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition | exact _root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition | (intros; apply _root_.GlobalTheory.KFinDecomp.cuspForm_kFinite_decomposition <;> assumption)
end
