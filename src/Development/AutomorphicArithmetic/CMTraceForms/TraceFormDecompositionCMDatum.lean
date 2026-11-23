module

import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.CMTraceForms.Places
import Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.NumberTheory.NumberField.Norm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs Formalism.L2.Pj UpperTheory.Depth

namespace UpperTheory.TraceSumEquivalence

private theorem exists_equiv (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) :
    ∃ Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O), ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E) := by
  classical
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hmem : ∀ (σ : E →ₐ[ℚ] C) (y : 𝓞 E), σ (y : E) ∈ (algebraMap O C).range := by
    intro σ y
    have hi : IsIntegral ℤ (σ (y : E)) :=
      (RingOfIntegers.isIntegral_coe y).map σ.toRingHom.toIntAlgHom
    have hi' : IsIntegral O (σ (y : E)) := hi.tower_top
    obtain ⟨z, hz⟩ := hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.mp hi')
    exact ⟨z, hz⟩
  let e : O ≃+* (algebraMap O C).range :=
    RingEquiv.ofLeftInverse (Function.leftInverse_invFun hinj)
  have he : ∀ z, algebraMap O C (e.symm z) = z := by
    intro z
    obtain ⟨a, ha⟩ := z.2
    show algebraMap O C (Function.invFun (algebraMap O C) z) = z
    exact Function.invFun_eq ⟨a, ha⟩
  let F : (E →ₐ[ℚ] C) → (𝓞 E →+* O) := fun σ =>
    e.symm.toRingHom.comp ((σ.toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _ (hmem σ))
  have hF : ∀ σ (y : 𝓞 E), algebraMap O C (F σ y) = σ (y : E) := fun σ y => he _
  have hFi : Function.Injective F := by
    intro σ τ h
    have h1 : σ.toRingHom.comp (algebraMap (𝓞 E) E) = τ.toRingHom.comp (algebraMap (𝓞 E) E) := by
      ext y
      have := congrArg (fun φ : 𝓞 E →+* O => algebraMap O C (φ y)) h
      simp only [hF] at this
      exact this
    have h2 : σ.toRingHom = τ.toRingHom :=
      IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h1
    exact AlgHom.coe_ringHom_injective h2
  have hFs : Function.Surjective F := by
    intro τ
    let g : 𝓞 E →+* C := (algebraMap O C).comp τ
    have hg : Function.Injective g := by
      rw [RingHom.injective_iff_ker_eq_bot]
      apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
      change Ideal.comap (algebraMap ℤ (𝓞 E)) (RingHom.ker g) = ⊥
      rw [RingHom.comap_ker]
      have : g.comp (algebraMap ℤ (𝓞 E)) = Int.castRingHom C := RingHom.ext_int _ _
      rw [this]
      exact (RingHom.injective_iff_ker_eq_bot _).mp Int.cast_injective
    refine ⟨(IsFractionRing.lift hg : E →+* C).toRatAlgHom, ?_⟩
    ext y
    apply hinj
    rw [hF]
    exact IsFractionRing.lift_algebraMap hg y
  exact ⟨Equiv.ofBijective F ⟨hFi, hFs⟩, hF⟩

private theorem trace_eq_sum (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type)
    [Field C] [IsAlgClosed C] [CharZero C] (O : Type) [CommRing O] [Algebra O C]
    [Algebra ℤ_[p] O] (Φ : (E →ₐ[ℚ] C) ≃ (𝓞 E →+* O))
    (hΦ : ∀ σ (y : 𝓞 E), algebraMap O C (Φ σ y) = σ (y : E)) (x : ℤ_[p] ⊗[ℤ] 𝓞 E) :
    algebraMap O C (algebraMap ℤ_[p] O (LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] x))) =
      ∑ σ : E →ₐ[ℚ] C, algebraMap O C (tauExt (Φ σ) x) := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    have hadd : LinearMap.mulLeft ℤ_[p] (a + b) = LinearMap.mulLeft ℤ_[p] a + LinearMap.mulLeft ℤ_[p] b := by
      ext z
      simp [add_mul]
    rw [hadd, map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, ← Finset.sum_add_distrib]
    simp [map_add (f := _)]
  | tmul c y =>
    have h0 : (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) = c • ((1 : ℤ_[p]) ⊗ₜ[ℤ] y) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h1 : LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E) =
        c • (Algebra.lmul ℤ (𝓞 E) y).baseChange ℤ_[p] := by
      rw [Algebra.baseChange_lmul, h0]
      ext z
      simp [smul_mul_assoc]
    have h2 : LinearMap.trace ℤ_[p] _ (LinearMap.mulLeft ℤ_[p] (c ⊗ₜ[ℤ] y : ℤ_[p] ⊗[ℤ] 𝓞 E)) =
        c * ((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℤ_[p]) := by
      rw [h1, map_smul, LinearMap.trace_baseChange, smul_eq_mul, Algebra.trace_apply]
      simp
    have h3 : ∑ σ : E →ₐ[ℚ] C, σ (y : E) = (((Algebra.trace ℤ (𝓞 E) y : ℤ) : ℚ) : C) := by
      rw [Algebra.coe_trace_int, ← eq_ratCast (algebraMap ℚ C), trace_eq_sum_embeddings]
    rw [h2]
    simp only [tauExt, Algebra.TensorProduct.lift_tmul, map_mul]
    have h4 : ∀ σ : E →ₐ[ℚ] C, algebraMap O C ((Φ σ).toIntAlgHom y) = σ (y : E) := fun σ => hΦ σ y
    simp only [h4, Algebra.ofId_apply, ← Finset.mul_sum, h3, map_intCast, Rat.cast_intCast]

end UpperTheory.TraceSumEquivalence


open UpperTheory.TraceSumEquivalence in
theorem UpperTheory.trace_form_decomposition_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Algebra ℤ_[p] O] (e : ℤ_[p] ⊗[ℤ] 𝓞 E), e * e = e →
      Nonempty (Fin (Module.finrank ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] e))) ≃ Emb (O := O) e) ∧ Nat.card (𝓞 E →+* O) = Module.finrank ℚ E := by
  apply GlobalTheory.EmbCount.card_emb <;> assumption
