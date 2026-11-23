module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Integral

@[expose] public section

open IsLocalRing



namespace GlobalTheory

open Polynomial TensorProduct

theorem tensor_exists_smul_eq_eval₂ (S K L : Type) [CommRing S] [IsDomain S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L]
    [IsScalarTower S K L] [FiniteDimensional K L] (π : S) (e : ℕ) (D : Type) [CommRing D]
    [Algebra S D] (φ : D ≃ₐ[S] AdjoinRoot (X ^ e - C π)) (z : TensorProduct S D L) :
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (TensorProduct S D L) s * z =
        f.eval₂ ((Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).comp
            (integralClosure S L).val).toRingHom
          (algebraMap D (TensorProduct S D L) (φ.symm (AdjoinRoot.root (X ^ e - C π)))) := by
  set gA : integralClosure S L →ₐ[S] TensorProduct S D L :=
    (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).comp (integralClosure S L).val
  set t := φ.symm (AdjoinRoot.root (X ^ e - C π))
  have hg : ∀ s : S, gA.toRingHom (algebraMap S (integralClosure S L) s) =
      algebraMap S (TensorProduct S D L) s := fun s => gA.commutes s
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 1, one_ne_zero, by simp⟩
  | tmul d l =>
    have hl : IsAlgebraic S l :=
      (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨s, hs, hint⟩ := hl.exists_integral_multiple
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (φ d)
    have hd : d = aeval t p := by
      rw [aeval_algHom_apply, AdjoinRoot.aeval_eq, hp]
      simp [t]
    refine ⟨C ⟨s • l, hint⟩ * p.map (algebraMap S (integralClosure S L)), s, hs, ?_⟩
    rw [eval₂_mul, eval₂_C, eval₂_map]
    have : (gA.toRingHom.comp (algebraMap S (integralClosure S L))) =
        algebraMap S (TensorProduct S D L) := RingHom.ext hg
    rw [this, ← aeval_def]
    have h2 : aeval (algebraMap D (TensorProduct S D L) t) p =
        algebraMap D (TensorProduct S D L) d := by
      rw [hd, aeval_algebraMap_apply]
    rw [h2]
    simp only [gA, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.coe_comp,
      Function.comp_apply, Subalgebra.coe_val, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Algebra.smul_def, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨f₁, s₁, hs₁, h₁⟩ := hx
    obtain ⟨f₂, s₂, hs₂, h₂⟩ := hy
    refine ⟨C (algebraMap S _ s₂) * f₁ + C (algebraMap S _ s₁) * f₂, s₁ * s₂,
      mul_ne_zero hs₁ hs₂, ?_⟩
    rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, hg, hg, ← h₁, ← h₂, map_mul]
    ring

theorem normalisation_mul_eq_aeval_root (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (φ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
    (b : integralClosure D (TensorProduct S D L)) :
    ∃ (f : Polynomial (integralClosure S L)) (s : S), s ≠ 0 ∧
      algebraMap S (integralClosure D (TensorProduct S D L)) s * b =
        Polynomial.aeval (algebraMap D (integralClosure D (TensorProduct S D L))
          (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)))) f := by
  obtain ⟨f, s, hs, h⟩ := tensor_exists_smul_eq_eval₂ S K L π e D φ (b : TensorProduct S D L)
  refine ⟨f, s, hs, Subtype.ext ?_⟩
  rw [aeval_def]
  have hc := Polynomial.hom_eval₂ f
    (algebraMap (integralClosure S L) (integralClosure D (TensorProduct S D L)))
    (integralClosure D (TensorProduct S D L)).val.toRingHom
    (algebraMap D (integralClosure D (TensorProduct S D L))
      (φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π))))
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.coe_val] at hc
  rw [hc]
  convert h using 2 <;> first | rfl | exact RingHom.ext fun _ => rfl
end GlobalTheory
