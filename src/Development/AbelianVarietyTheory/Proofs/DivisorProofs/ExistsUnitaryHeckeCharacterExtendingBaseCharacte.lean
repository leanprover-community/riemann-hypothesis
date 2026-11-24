module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour", "h": "module\n\npublic import Mathlib.Analysis.Complex.Norm\npublic import Mathlib.NumberTheory.NumberField.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.CStarAlgebra.Classes\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff\nimport Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul\nimport Formalism.LocalToGlobal.IndefiniteReal.DatumF\nimport Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Mathlib.Analysis.Normed.Ring.Basic\npublic import Mathlib.NumberTheory.NumberField.Norm\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF GlobalTheory.HeckeExtend

namespace GlobalTheory

theorem nat_le_four_of_dvd_of_embeddings_le_four :
    ∀ (F : Type) [Field F] [NumberField F] (y : F) (m : ℕ) (r : 𝓞 F), y ≠ 0 → y = m * r →
    (∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4) → m ≤ 4 := by
  intro F _ _ y m r hy hyr hφ
  set d := Module.finrank ℚ F with hd
  have hr : (r : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, mul_zero]
  have hm : (m : F) ≠ 0 := by rintro h; apply hy; rw [hyr, h, zero_mul]
  have hN : Algebra.norm ℚ y = (m : ℚ) ^ d * (Algebra.norm ℤ r : ℚ) := by
    rw [hyr, map_mul, Algebra.coe_norm_int]
    congr 1
    rw [show ((m : F)) = algebraMap ℚ F (m : ℚ) by simp, Algebra.norm_algebraMap]
  have hr0 : (Algebra.norm ℤ r : ℚ) ≠ 0 := by
    rw [Algebra.coe_norm_int]; exact (Algebra.norm_ne_zero_iff).2 hr
  have hr1 : (1 : ℝ) ≤ |((Algebra.norm ℤ r : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ r ≠ 0 := by exact_mod_cast hr0
    exact_mod_cast Int.one_le_abs this
  have hlow : (m : ℝ) ^ d ≤ |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    rw [hN]; push_cast
    rw [abs_mul, abs_pow, Nat.abs_cast]
    nlinarith [pow_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) d]
  have hprod := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  have hup : |((Algebra.norm ℚ y : ℚ) : ℝ)| ≤ 4 ^ d := by
    have h1 : ‖algebraMap ℚ ℂ (Algebra.norm ℚ y)‖ = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
      simp
    rw [← h1, hprod, norm_prod]
    calc ∏ σ : F →ₐ[ℚ] ℂ, ‖σ y‖ ≤ ∏ _σ : F →ₐ[ℚ] ℂ, (4 : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun σ _ => hφ σ.toRingHom)
      _ = 4 ^ d := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card]
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have : (m : ℝ) ≤ 4 := (pow_le_pow_iff_left₀ (Nat.cast_nonneg m) (by norm_num) hd0).1 (hlow.trans hup)
  exact_mod_cast this

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntFOneMul\npublic import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceKernelIdeleCharacterTrivialAtInfStatement\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerOfAlgebraMapMemAdelesFiniteMultiple\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSmulMemAdelesFiniteMultipleOfTensorCongru\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIntegralTensorAdeleMultiples\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorCongruenceOfSupportedAtInfinityStatement\npublic import Mathlib.Analysis.Complex.Norm\npublic import Mathlib.NumberTheory.NumberField.Basic\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatLeFourOfDvdOfEmbeddingsLeFour\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Int\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open GlobalTheory.HeckeExtend

noncomputable section

namespace GlobalTheory.HeckeExtend

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem intF_half {x : AF F} {M : ℕ} (h : 2 • x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨c, hc, ?_⟩
  change 2 • x.2 = (2 * M) • c at e
  have h2 : IsUnit (2 : Af F) := by
    have : algebraMap F (Af F) 2 = 2 := map_ofNat _ 2
    rw [← this]
    exact (IsUnit.mk0 (2 : F) two_ne_zero).map _
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul, mul_assoc, Nat.cast_ofNat] at e
  rw [nsmul_eq_mul]
  exact h2.mul_left_cancel e

theorem intF_le {x : AF F} {M : ℕ} (h : x ∈ intF F (2 * M)) : x ∈ intF F M := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨2 • c, fun v => ?_, ?_⟩
  · have : (2 • c) v = c v + c v := by rw [two_nsmul]; rfl
    rw [this]
    exact add_mem (hc v) (hc v)
  · rw [e, smul_smul, mul_comm]

theorem CE_cA (σ : E →ₐ[F] E) {N : ℕ} {z : AF F ⊗[F] E} (h : z ∈ CE F E N) : cA σ z ∈ CE F E N := by
  obtain ⟨s, hs, e⟩ := mem_CE.1 h
  exact mem_CE.2 ⟨cA σ s, cA_mem_SE σ hs, by rw [← e, map_nsmul]⟩

theorem incAF_algebraMap (y : F) :
    incAF F E (algebraMap F E y) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) := by
  show (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (algebraMap F E y) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply F (AF F) (AF F ⊗[F] E)]

theorem exists_emb_ext (φ : F →+* ℂ) : ∃ τ : E →+* ℂ, τ.comp (algebraMap F E) = φ := by
  letI : Algebra F ℂ := φ.toAlgebra
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  exact ⟨(IsAlgClosed.lift : E →ₐ[F] ℂ).toRingHom, (IsAlgClosed.lift : E →ₐ[F] ℂ).comp_algebraMap⟩

theorem key (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (hM : 0 < M)
    (lam : (AF F)ˣ →* Circle) (h1 : ∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1)
    (hMk : ∀ b : (AF F)ˣ, (b : AF F) - 1 ∈ intF F M → ((b⁻¹ : (AF F)ˣ) : AF F) - 1 ∈ intF F M → lam b = 1)
    (a : (AF F)ˣ) (ha : idFF F E a ∈ (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)) :
    lam a = 1 := by
  obtain ⟨hσσ, hfix⟩ := _root_.GlobalTheory.CMConjInvol.cm_conj_invol_fixed F E σ hcm
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have htr : ∀ (N : ℕ) (x : AF F), algebraMap (AF F) (AF F ⊗[F] E) x ∈ CE F E (2 * (2 * N)) → x ∈ intF F N := by
    intro N x hx
    have := _root_.GlobalTheory.HeckeExtend.TraceCE.finrank_smul_mem_intF F E _ x hx
    rw [h2] at this
    exact intF_le (intF_half this)
  have hcongF : ∀ b : (AF F)ˣ, idFF F E b ∈ WE F E (8 * M) → lam b = 1 := by
    intro b hb
    have e8 : 8 * M = 2 * (2 * (2 * M)) := by ring
    refine hMk b (intF_le (htr (2 * M) _ ?_)) (intF_le (htr (2 * M) _ ?_))
    · rw [← e8, map_sub, map_one]
      exact hb.1
    · rw [← e8, map_sub, map_one]
      have := hb.2
      rwa [← map_inv] at this
  obtain ⟨y, ⟨k, rfl⟩, w, hw, hyw⟩ := Subgroup.mem_sup.1 ha
  let cU : (AF F ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := Units.map (cA σ).toMonoidHom
  have hcW : ∀ z ∈ WE F E (8 * M), cU z ∈ WE F E (8 * M) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have := CE_cA σ hz.1
      rwa [map_sub, map_one] at this
    · have := CE_cA σ hz.2
      rw [map_sub, map_one] at this
      rw [← map_inv]
      exact this
  have hfixa : cU (idFF F E a) = idFF F E a := Units.ext ((cA σ).commutes (a : AF F))
  have hcinc : cU (Units.map (incAF F E).toMonoidHom k) =
      Units.map (incAF F E).toMonoidHom (Units.map σ.toMonoidHom k) := Units.ext rfl
  let ζ : Eˣ := Units.map σ.toMonoidHom k * k⁻¹
  have hζW : Units.map (incAF F E).toMonoidHom ζ ∈ WE F E (8 * M) := by
    have e1 := congrArg cU hyw
    rw [map_mul, hfixa, hcinc, ← hyw] at e1
    have : Units.map (incAF F E).toMonoidHom ζ = w * (cU w)⁻¹ := by
      simp only [ζ, map_mul, map_inv]
      rw [mul_inv_eq_iff_eq_mul, mul_right_comm, eq_mul_inv_iff_mul_eq, e1, mul_comm]
    rw [this]
    exact mul_mem hw (inv_mem (hcW w hw))
  have hζv : (ζ : E) = σ k * (k : E)⁻¹ := by simp [ζ]
  have hζ1 : (ζ : E) = 1 := by
    by_contra hne
    set x : E := (ζ : E) - 1 with hxdef
    have hx0 : x ≠ 0 := sub_ne_zero.2 hne
    have hxC : incAF F E x ∈ CE F E (8 * M) := by
      have := hζW.1
      rw [hxdef, map_sub, map_one]
      exact this
    obtain ⟨s, hs, hsx⟩ := mem_CE.1 hxC
    have hσx : incAF F E (σ x) = cA σ (incAF F E x) := rfl
    obtain ⟨y, hy⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
    have hyC : algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) y) ∈ CE F E (2 * (2 * (16 * M * M))) := by
      rw [← incAF_algebraMap, hy, map_mul, hσx, ← hsx, map_nsmul]
      refine mem_CE.2 ⟨s * cA σ s, SE_mul hs (cA_mem_SE σ hs), ?_⟩
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have hyI := htr (16 * M * M) _ hyC
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.HeckeExtend.exists_int_of_mem_intF F y (16 * M * M) (by positivity) hyI
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact mul_ne_zero hx0 ((map_ne_zero σ).2 hx0) hy.symm
    have hbound : ∀ φ : F →+* ℂ, ‖φ y‖ ≤ 4 := by
      intro φ
      obtain ⟨τ, hτ⟩ := exists_emb_ext (E := E) φ
      have hφ : φ y = τ (algebraMap F E y) := by rw [← hτ]; rfl
      have hτσ := hcm.2.2.2 τ
      have hk0 : τ (k : E) ≠ 0 := (map_ne_zero τ).2 k.ne_zero
      have hζn : ‖τ (ζ : E)‖ = 1 := by
        rw [hζv, map_mul, map_inv₀, hτσ, norm_mul, norm_inv, norm_star]
        exact mul_inv_cancel₀ (norm_ne_zero_iff.2 hk0)
      have hxn : ‖τ x‖ ≤ 2 := by
        calc ‖τ x‖ = ‖τ (ζ : E) - 1‖ := by rw [hxdef, map_sub, map_one]
        _ ≤ ‖τ (ζ : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hζn, norm_one]; norm_num
      rw [hφ, hy, map_mul, hτσ, norm_mul, norm_star]
      nlinarith [norm_nonneg (τ x)]
    have := _root_.GlobalTheory.nat_le_four_of_dvd_of_embeddings_le_four F y (16 * M * M) r hy0 hr hbound
    nlinarith
  have hk : σ k = (k : E) := by
    rw [hζv] at hζ1
    exact (mul_inv_eq_one₀ k.ne_zero).1 hζ1
  obtain ⟨f, hf⟩ := hfix k hk
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact k.ne_zero hf.symm
  let fU : (AF F)ˣ := Units.map (algebraMap F (AF F)).toMonoidHom (Units.mk0 f hf0)
  have hinc : Units.map (incAF F E).toMonoidHom k = idFF F E fU := by
    apply Units.ext
    show incAF F E (k : E) = algebraMap (AF F) (AF F ⊗[F] E) (algebraMap F (AF F) f)
    rw [← hf, incAF_algebraMap]
  have hw' : w = idFF F E (fU⁻¹ * a) := by
    rw [map_mul, map_inv, ← hinc, ← hyw]
    group
  have hb := hcongF (fU⁻¹ * a) (hw' ▸ hw)
  have hfU : lam fU = 1 := h1 (Units.mk0 f hf0)
  have : a = fU * (fU⁻¹ * a) := by group
  rw [this, map_mul, hfU, hb, mul_one]

theorem exists_extend_hecke : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ lam : (AF F)ˣ →* Circle, Continuous lam →
      (∀ a : Fˣ, lam (Units.map (algebraMap F (AF F)).toMonoidHom a) = 1) →
      (∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) → lam a = 1) →
      ∃ lam' : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF lam' ∧
        (∀ z : (AF F ⊗[F] E)ˣ, At (evI F) ((z : AF F ⊗[F] E) - 1) → lam' z = 1) ∧
        ∀ a, lam' (idFF F E a) = lam a := by
  intro F E _ _ _ _ _ σ B hB lam hc h1 hinf
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨M, hM, hMk⟩ := _root_.GlobalTheory.HeckeExtend.exists_cong_ker F lam hc hinf
  let V : Subgroup (AF F ⊗[F] E)ˣ := (Units.map (incAF F E).toMonoidHom).range ⊔ WE F E (8 * M)
  have hkey : ∀ a : (AF F)ˣ, idFF F E a ∈ V → lam a = 1 := key σ hB.cm M hM lam h1 hMk
  have hN : 0 < 8 * M := by positivity
  have hWo : IsOpen (WE F E (8 * M) : Set (AF F ⊗[F] E)ˣ) := by
    have ho := _root_.GlobalTheory.HeckeExtend.CE_isOpen F E (8 * M) hN
    have hcv : Continuous fun z : (AF F ⊗[F] E)ˣ => (z : AF F ⊗[F] E) - 1 :=
      Units.continuous_val.sub continuous_const
    have hci : Continuous fun z : (AF F ⊗[F] E)ˣ => ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 :=
      Units.continuous_coe_inv.sub continuous_const
    exact (ho.preimage hcv).inter (ho.preimage hci)
  have hVo : IsOpen (V : Set (AF F ⊗[F] E)ˣ) := Subgroup.isOpen_mono le_sup_right hWo

  let ψ0 : (AF F)ˣ →* (AF F ⊗[F] E)ˣ ⧸ V := (QuotientGroup.mk' V).comp (idFF F E)
  have hker : ψ0.ker ≤ lam.ker := fun a ha => hkey a ((QuotientGroup.eq_one_iff _).1 ha)
  letI : DivisibleBy (Additive Circle) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn u => by
    obtain ⟨t, ht⟩ := Circle.exp_surjective u.toMul
    refine ⟨Additive.ofMul (Circle.exp (t / n)), ?_⟩
    show Additive.ofMul (Circle.exp (t / n) ^ n) = u
    rw [← Circle.exp_nsmul, nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 hn), ht]
    rfl
  letI : DivisibleBy (Additive Circle) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive Circle)).extension_property_addMonoidHom
    (MonoidHom.toAdditive (QuotientGroup.kerLift ψ0)) (QuotientGroup.kerLift_injective ψ0)
    (MonoidHom.toAdditive (QuotientGroup.lift ψ0.ker lam hker))
  let κ : (AF F ⊗[F] E)ˣ ⧸ V →* Circle := MonoidHom.toAdditive.symm ρ
  have hκ : ∀ x, κ (QuotientGroup.kerLift ψ0 x) = QuotientGroup.lift ψ0.ker lam hker x :=
    fun x => DFunLike.congr_fun hρ (Additive.ofMul x)
  have hV1 : ∀ z ∈ V, κ.comp (QuotientGroup.mk' V) z = 1 := fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]
  refine ⟨κ.comp (QuotientGroup.mk' V), ⟨?_, fun x => hV1 _ (le_sup_left (a := (Units.map (incAF F E).toMonoidHom).range)
    ⟨x, rfl⟩)⟩, fun z hz => hV1 z (le_sup_right (a := (Units.map (incAF F E).toMonoidHom).range) ?_), fun a => hκ (a : (AF F)ˣ ⧸ ψ0.ker)⟩
  · refine continuous_of_continuousAt_one _ ?_
    unfold ContinuousAt
    rw [map_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hVo.mem_nhds (one_mem V)] with z hz
    exact (hV1 z hz).symm
  · have hN' := hN
    refine ⟨GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ hz, GlobalTheory.T.mem_tensorCongruence_of_supported_at_infinity F E _ hN' _ ?_⟩
    intro u hu
    have e : ((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) - 1 = -(((z⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * ((z : AF F ⊗[F] E) - 1)) := by
      rw [mul_sub, Units.inv_mul, mul_one, neg_sub]
    rw [e, smul_neg, ← mul_smul_comm, hz u hu, mul_zero, neg_zero]

end GlobalTheory.HeckeExtend

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterExtendingBaseCharacte =====
