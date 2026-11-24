module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section ULim

variable {ι R : Type} [CommRing R] (F : Filter ι) (I : ℕ → Ideal R)
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def uNull : Submodule R (∀ i, M i) where
  carrier := {p | ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i))}
  add_mem' ha hb j := ((ha j).and (hb j)).mono fun _ h => add_mem h.1 h.2
  zero_mem' _ := Eventually.of_forall fun _ => zero_mem _
  smul_mem' c _ h j := (h j).mono fun _ h => Submodule.smul_mem _ c h


abbrev ULim : Type := (∀ i, M i) ⧸ uNull F I M

def ULim.mk : (∀ i, M i) →ₗ[R] ULim F I M := (uNull F I M).mkQ

theorem ULim.mk_surjective : Function.Surjective (ULim.mk F I M) := Submodule.mkQ_surjective _

variable {F I M} in
theorem ULim.mk_eq_zero {p : ∀ i, M i} :
    ULim.mk F I M p = 0 ↔ ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i)) := by
  show (uNull F I M).mkQ p = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl


variable {I M} in
def ULim.map {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) : ULim F I M →ₗ[R] ULim F I' M' :=
  Submodule.mapQ _ _ (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) fun p hp j =>
    (hp j).mono fun i hi => by
      have h1 : f i (p i) ∈ Submodule.map (f i) (I j • ⊤ : Submodule R (M i)) := ⟨_, hi, rfl⟩
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono (h j) le_top h1

variable {I M} in
theorem ULim.map_mk {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) (p : ∀ i, M i) :
    ULim.map F h f (ULim.mk F I M p) = ULim.mk F I' M' fun i => f i (p i) := rfl

def ULim.scal (r : ι → R) : ULim F I M →ₗ[R] ULim F I M :=
  ULim.map F (fun _ => le_rfl) fun i => r i • LinearMap.id



end ULim

section QReg

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def QRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) (J : Ideal R) (a : ℕ) : Prop :=
  ∀ c : GlobalTheory.MonoDeg σ a → M,
    ∑ α, GlobalTheory.monoVal y α.1 • c α ∈ ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ ((Ideal.span (Set.range y) ⊔ J) • ⊤ : Submodule R M)

theorem isQuasiRegularSeq_iff_qRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) :
    GlobalTheory.IsQuasiRegularSeq M y ↔ ∀ a, QRegAt M y ⊥ a := by
  unfold GlobalTheory.IsQuasiRegularSeq QRegAt
  simp only [sup_bot_eq]

end QReg

end UpperTheory.V.AlgebraTools
