module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenMapTmulEq
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

variable (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
  [Algebra ℚ B] [IsScalarTower ℚ F B]

theorem cenMap_tmul (q : ℚ_[ℓ]) (f : F) : cenMap ℓ F B (q ⊗ₜ f) = q ⊗ₜ algebraMap F B f := by
  simp [cenMap]

theorem cenMap_mem (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ)
    {a : ℚ_[ℓ] ⊗[ℚ] F} (ha : a ∈ cenOrder ℓ F) : cenMap ℓ F B a ∈ locOrder ℓ Λ := by
  have h : cenOrder ℓ F ≤ (locOrder ℓ Λ).comap ((cenMap ℓ F B).restrictScalars ℤ_[ℓ]) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, rfl⟩
    show cenMap ℓ F B _ ∈ locOrder ℓ Λ
    rw [cenMap_tmul]
    exact Algebra.subset_adjoin ⟨_, hΛ a, rfl⟩
  exact h ha

theorem cenMap_commute (a : ℚ_[ℓ] ⊗[ℚ] F) (y : ℚ_[ℓ] ⊗[ℚ] B) : Commute (cenMap ℓ F B a) y := by
  first
  | exact @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap
  | (apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CentralizerMapTensor.commute_cenMap <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CentralizerMapTensor.commute_cenMap ..)

def cenIncl (Λ : Subring B) (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    cenOrder ℓ F →ₐ[ℤ_[ℓ]] locOrder ℓ Λ :=
  (((cenMap ℓ F B).restrictScalars ℤ_[ℓ]).comp (cenOrder ℓ F).val).codRestrict (locOrder ℓ Λ)
    (fun a => cenMap_mem ℓ F B Λ hΛ a.2)

theorem coe_cenIncl (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    (cenIncl ℓ F B Λ hΛ a : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B a := rfl

def cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    Algebra (cenOrder ℓ F) (locOrder ℓ Λ) :=
  (cenIncl ℓ F B Λ hΛ).toRingHom.toAlgebra' fun a x => Subtype.ext (cenMap_commute ℓ F B a x)

theorem algebraMap_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) (a : cenOrder ℓ F) :
    letI := cenAlgebra ℓ F B Λ hΛ
    algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a = cenIncl ℓ F B Λ hΛ a := rfl

theorem isScalarTower_cenAlgebra (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) :
    letI := cenAlgebra ℓ F B Λ hΛ
    IsScalarTower ℤ_[ℓ] (cenOrder ℓ F) (locOrder ℓ Λ) := by
  letI := cenAlgebra ℓ F B Λ hΛ
  exact IsScalarTower.of_algebraMap_eq fun r => ((cenIncl ℓ F B Λ hΛ).commutes r).symm

end GlobalTheory.LocMatrix
