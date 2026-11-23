module

public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroSmulMemSpan
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

@[expose] public section

open NumberField

namespace GlobalTheory.IntFormsRank

variable {LL : Type} [Field LL] [NumberField LL] {n : ℕ}

theorem smul_eq_algebraMap_smul (r : 𝓞 LL) (z : Fin n → LL) : r • z = (algebraMap (𝓞 LL) LL r) • z :=
  (algebraMap_smul LL r z).symm

theorem exists_den_smul_mem (T : Set (Fin n → LL)) (x : Fin n → LL) (hx : x ∈ Submodule.span LL T) :
    ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  first
  | exact @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span
  | (apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroMultipleInSpan.exists_ne_zero_smul_mem_span ..)

theorem span_inf_eq (T : Set (Fin n → LL)) (hT : Submodule.span LL T = ⊤) (S : Submodule LL (Fin n → LL)) :
    Submodule.span LL ((Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) :
      Set (Fin n → LL)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    have hxT : x ∈ Submodule.span LL T := by rw [hT]; exact Submodule.mem_top
    obtain ⟨d, hd, hdx⟩ := exists_den_smul_mem T x hxT
    have hdL : algebraMap (𝓞 LL) LL d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 LL) LL)]; exact hd
    have hmem : d • x ∈ (Submodule.span (𝓞 LL) T ⊓ S.restrictScalars (𝓞 LL) : Submodule (𝓞 LL) (Fin n → LL)) := by
      refine ⟨hdx, ?_⟩
      show d • x ∈ S
      rw [smul_eq_algebraMap_smul]; exact S.smul_mem _ hx
    have hx' : x = (algebraMap (𝓞 LL) LL d)⁻¹ • (d • x) := by
      rw [smul_eq_algebraMap_smul, smul_smul, inv_mul_cancel₀ hdL, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.IntFormsRank

theorem GlobalTheory.IntFormsRank.rkK_Mall : ∀ (LL Ks : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] (n : ℕ)
    (Wσ : (LL →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (Wσ σ)] [∀ σ, InnerProductSpace ℂ (Wσ σ)]
    (G0 : Type) [Group G0] [Fintype G0] (A : Formalism.IndefR.Arith.FormsL LL Ks (Fin n → LL) Wσ G0) (J0 : Subgroup G0)
    (lam0 : J0 →* LLˣ) (f : (Fin n → LL) →ₗ[LL] (Fin n → LL)),
    Submodule.span LL (A.MK : Set (Fin n → LL)) = ⊤ →
    Formalism.HN.rkK (A.Mall J0 lam0) = Module.finrank LL (A.typeP J0 lam0) ∧
    Formalism.HN.rkK (A.Mall J0 lam0 ⊓ (LinearMap.ker f).restrictScalars (𝓞 LL)) =
      Module.finrank LL (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)) := by
  intro LL Ks _ _ _ _ _ n Wσ _ _ G0 _ _ A J0 lam0 f hsp
  constructor
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    rw [GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
  · unfold Formalism.HN.rkK Formalism.IndefR.Arith.FormsL.Mall
    have e : (Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓ (A.typeP J0 lam0).restrictScalars (𝓞 LL) ⊓
        (LinearMap.ker f).restrictScalars (𝓞 LL)) =
        Submodule.span (𝓞 LL) (A.MK : Set (Fin n → LL)) ⊓
          (A.typeP J0 lam0 ⊓ LinearMap.ker f : Submodule LL (Fin n → LL)).restrictScalars (𝓞 LL) := by
      rw [inf_assoc]; rfl
    rw [e, GlobalTheory.IntFormsRank.span_inf_eq _ hsp]
