module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.ModuLR

open Filter
open scoped RestrictedProduct

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

theorem cofinite_le_principal_compl :
    cofinite ≤ 𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [le_principal_iff]; exact S.finite_toSet.compl_mem_cofinite


open Classical in
def jSP : SPart F S × OPart F S →
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  fun p => ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v), by
    rw [eventually_principal]
    intro v hv
    have hv' : v ∉ S := hv
    simp only [dif_neg hv']
    exact (p.2 ⟨v, hv'⟩).2⟩

def jSPinv : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] →
    SPart F S × OPart F S :=
  fun x => (fun v => x v.1, fun v => ⟨x v.1, x.2 v.2⟩)

theorem continuous_jSP : Continuous (jSP F S) := by
  rw [RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff]
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => p.1 ⟨v, h⟩ := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact (continuous_apply _).comp continuous_fst
  · have : (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
        = fun p => ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      funext p; simp [jSP, h]
    show Continuous (fun p : SPart F S × OPart F S => ((jSP F S p : _) : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v)
    rw [this]; exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)

theorem continuous_jSPinv : Continuous (jSPinv F S) := by
  have hc : Continuous (fun x : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] =>
      (x : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F)) :=
    RestrictedProduct.isEmbedding_coe_of_principal.continuous
  refine Continuous.prodMk (continuous_pi fun v => (continuous_apply v.1).comp hc)
    (continuous_pi fun v => ((continuous_apply v.1).comp hc).subtype_mk _)

def jSPHomeo : SPart F S × OPart F S ≃ₜ
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, (v.adicCompletionIntegers F : Set (v.adicCompletion F))]_[𝓟 ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] where
  toFun := jSP F S
  invFun := jSPinv F S
  left_inv p := by
    ext v
    · simp [jSP, jSPinv, v.2]
    · simp [jSP, jSPinv, v.2]
  right_inv x := by
    ext v
    by_cases h : v ∈ S <;> simp [jSP, jSPinv, h]
  continuous_toFun := continuous_jSP F S
  continuous_invFun := continuous_jSPinv F S

theorem jS_eq_comp : (jS F S : SPart F S × OPart F S → Af F) =
    RestrictedProduct.inclusion _ _ (cofinite_le_principal_compl F S) ∘ jSP F S := by
  funext p; rfl

theorem isOpenEmbedding_jS : IsOpenEmbedding (jS F S) := by
  rw [jS_eq_comp]
  exact (RestrictedProduct.isOpenEmbedding_inclusion_principal
    (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F)) (cofinite_le_principal_compl F S)).comp
    (jSPHomeo F S).isOpenEmbedding

end GlobalTheory.ModuLR
