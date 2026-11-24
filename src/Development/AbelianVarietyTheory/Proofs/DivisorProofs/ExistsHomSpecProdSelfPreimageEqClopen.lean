module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn

namespace GlobalTheory

theorem exists_hom_spec_prod_self_preimage_eq_clopen :
    ∀ (O : Type) [CommRing O] (T : Scheme.{0}) (p : T ⟶ Spec (.of O)) (U : Set T), IsClopen U →
      ∃ h : T ⟶ Spec (.of (O × O)), h ≫ twoπ O = p ∧
        ((h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : T.Opens) : Set T) = U := by
  intro O _ T p U hU
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen T U hU
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop).hom
  let ψ : O × O →+* Γ(T, ⊤) :=
    { toFun := fun x => φ x.1 * ε + φ x.2 * (1 - ε)
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination -(φ x.1 * φ y.1 - φ x.1 * φ y.2 - φ x.2 * φ y.1 + φ x.2 * φ y.2) * he
      map_zero' := by simp
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hψ : ψ.comp (algebraMap O (O × O)) = φ := by
    ext a
    change φ a * ε + φ a * (1 - ε) = φ a
    ring
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · have : CommRingCat.ofHom φ = (Scheme.ΓSpecIso (.of O)).inv ≫ p.appTop := rfl
    rw [Category.assoc, twoπ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, this, Spec.map_comp,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  · rw [Scheme.preimage_basicOpen_top, ← hεU]
    congr 2
    have h1 : (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)).appTop (fst1 O) = ψ ((1, 0) : O × O) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
      have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
      have h2 := congrArg (fun f => f.hom (fst1 O)) this
      simp only [CommRingCat.comp_apply, CommRingCat.hom_ofHom] at h2
      refine h2.trans ?_
      simp [fst1]
    rw [h1]
    change φ 1 * ε + φ 0 * (1 - ε) = ε
    simp

end GlobalTheory
