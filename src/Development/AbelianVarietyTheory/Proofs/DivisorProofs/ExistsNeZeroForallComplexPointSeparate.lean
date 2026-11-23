module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.FiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
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

namespace GlobalTheory

theorem exists_ne_zero_forall_complexPoint_separate
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

end GlobalTheory
