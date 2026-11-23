module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedJacquetSurvivalProductOfTwoGroups
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.twistedJacquet_survival_product_of_two_groups : ∀ (G₁ G₂ V : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G₁ × G₂) V), IsSmooth ρ → ∀ (U₁ : Subgroup G₁) (U₂ : Subgroup G₂) (J₁ : Set G₁) (J₂ : Set G₂) (θ₁ : G₁ → ℂ) (θ₂ : G₂ → ℂ), (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₁ W), IsSmooth σ → ∀ w ∈ twKer σ U₁ 1, IsEig σ J₁ θ₁ w → w = 0) → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G₂ W), IsSmooth σ → ∀ w ∈ twKer σ U₂ 1, IsEig σ J₂ θ₂ w → w = 0) → ∀ v ∈ twKer (ρ.comp (MonoidHom.inl G₁ G₂)) U₁ 1 ⊔ twKer (ρ.comp (MonoidHom.inr G₁ G₂)) U₂ 1, IsEig (ρ.comp (MonoidHom.inl G₁ G₂)) J₁ θ₁ v → IsEig (ρ.comp (MonoidHom.inr G₁ G₂)) J₂ θ₂ v → v = 0 := by
  first | exact @GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod | exact GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod | (intros; apply GlobalTheory.PsType.eq_zero_of_mem_sup_twKer_prod <;> assumption)
