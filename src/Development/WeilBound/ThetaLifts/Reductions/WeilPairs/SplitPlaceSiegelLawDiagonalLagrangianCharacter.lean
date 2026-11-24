module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsCompactOfFinite
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralCompAddEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SmulMemConjHalf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm, Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm", "h": "module\n\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacterIm\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalMatricesDiscreteCocompactAdelicMatrixSpa\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsCompactOfFinite\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralCompAddEquiv\nimport Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SmulMemConjHalf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

theorem exists_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ e, IsSplitIdemF σ e →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f₀ ≠ 0 →
      ∃ ℓ : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WOF F E nS (nT + nT), (∀ i j, cAF σ e * u i j = u i j) →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            ℓ (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
        (∃ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f ∧ ℓ f ≠ 0) ∧
        ∀ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det → ∃ R : ℝ, 0 < R ∧
          ∀ (f f' : WOF F E nS (nT + nT) → ℂ) (k : ℂ),
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f' →
            (∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
              prof σ JS JT ξ₀ B.ψ ν 𝓕 f' y = k * prof σ JS JT ξ₀ B.ψ ν 𝓕 f (M * y)) →
            ℓ f' = (R : ℂ) * k * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  letI : MeasurableSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := borel _
  haveI : BorelSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := GlobalTheory.SplitInvFormF.conjHalf σ e nS nT)).IsAddHaarMeasure
  have hth := GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f.1 y.1 ∂μ
      map_add' := fun f g => by
        rw [← integral_add (prof_integrable hB hS hT hξ hσξ hν h𝓕 he μ f.2)
          (prof_integrable hB hS hT hξ hσξ hν h𝓕 he μ g.2)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_add hB hν h𝓕 f.2 g.2 y.1)
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_smul ν 𝓕 c f.1 y.1) }
  obtain ⟨ℓ, hℓ0⟩ := LinearMap.exists_extend L
  have hℓ : ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
      ℓ f = ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1 ∂μ :=
    fun f hf => LinearMap.congr_fun hℓ0 ⟨f, hf⟩
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun M hM => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp (σ := σ) (e := e) hu
    rw [hℓ _ (hth _ _ hf), hℓ f hf,
      GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ ha) (mul_mem_conjHalf _ hb),
      ← integral_add_right_eq_self (μ := μ)
        (fun y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1) ⟨b, hb⟩]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ = prof σ JS JT ξ₀ B.ψ ν 𝓕 f (y.1 + b)
    simp only
    rw [prof_heis_dC hB hS hT hξ hσξ hν h𝓕 (hth _ _ hf), GlobalTheory.SplitVacF.commF_half he y.2 (add_mem ha ha), one_mul,
      prof_heis_aC ν 𝓕 he f y.2 hb]
  · by_contra hall
    push Not at hall
    exact hne (lagrInt_eq_zero hB hS hT hξ hσξ hν h𝓕 he μ hf₀ fun u => by
      rw [← hℓ _ (hth u _ hf₀)]; exact hall _ (hth u _ hf₀))
  · obtain ⟨r, hr, hm⟩ := integral_mul_left e μ M hM
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← hm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitLagrF

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm =====

-- ===== clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter =====
-- clump-header: {"m": "Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionHeisenbergInvariant\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.CAFInvol\npublic import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

theorem circle_eq_one_of_pos {u : Circle} {t : ℝ} (ht : 0 < t) (h : (u : ℂ) = t) : u = 1 := by
  have h1 : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
  apply Circle.ext
  rw [h, h1, Circle.coe_one]
  simp

theorem mtF_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : mtF σ J 1 = 1 := by
  unfold mtF; rw [map_one]; rfl

theorem suppAtF_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : AF F ⊗[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : SuppAtF σ e J 1 := by
  intro i j
  rw [mtF_one', sub_self, Matrix.zero_apply, mul_zero]

theorem isDetAtF_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (e : AF F ⊗[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : IsDetAtF σ e J 1 1 := by
  show ((1 : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = e * (mtF σ J 1).det + (1 - e)
  rw [mtF_one', Matrix.det_one, Units.val_one]; ring

theorem modu_pos {F : Type} [Field F] [NumberField F] (x : (AF F)ˣ) : 0 < ((adeleClass F).modu x : ℝ) := by
  have h : (adeleClass F).modu x * (adeleClass F).modu x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h0 : (adeleClass F).modu x ≠ 0 := left_ne_zero_of_mul_eq_one h
  exact lt_of_le_of_ne (NNReal.coe_nonneg _) (by exact_mod_cast h0.symm)

end GlobalTheory.SplitLagrF

open GlobalTheory.SplitLagrF in
theorem PositivityTheory.ThKW.lagrangian_integral_parseval : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle,
        (∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f) →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f₀ ≠ 0 →
      ∀ e, IsSplitIdemF σ e → ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        (∀ i j, (e + cAF σ e) * (t.1 - 1) i j = (t.1 - 1) i j) → α t = χS (Matrix.GeneralLinearGroup.det t) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd α hlaw f₀ hf₀ hne e he t ht
  obtain ⟨h, hhC, hsupp, ⟨M, hM, hMy⟩, x, hx, hχx⟩ := exists_levi F E σ B hB nT JT hT e he t ht
  obtain ⟨ℓ, hinv, ⟨f, hf, hℓf⟩, hcmp⟩ := exists_form F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨R, hR, hRk⟩ := hcmp M hM
  obtain ⟨r, hr, hsp⟩ := hωd.om_split e he 1 h (suppAtF_one σ e JS) hsupp 1 x (isDetAtF_one σ e JS) hx
  set m : ℝ := (((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F)
    (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) with hm_def
  have hm : 0 < m := Real.rpow_pos_of_pos (modu_pos _) _
  have h1 := hsp ℓ hinv f hf
  have h2 : ℓ (ωd (1, h) f) = (R : ℂ) * ((α t : ℂ) * (m : ℂ)) * ℓ f := by
    refine hRk f (ωd (1, h) f) _ hf (hωd.om_pres _ f hf) (fun y _ => ?_)
    have hth : IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (aC F E nT * (M * y)) f) :=
      GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS (nT + nT) JS _ ξ₀ _ f hf
    have hh := hωd.om_heis 1 h (aC F E nT * (M * y)) f hf
    have hact : actOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) 1 h (aC F E nT * (M * y)) = aC F E nT * y := by
      unfold actOF
      rw [← hMy nS y, ← Matrix.mul_assoc, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, inv_one]
      simp only [mtF_one', Matrix.one_mul, Matrix.mul_one]
    unfold prof
    rw [← hact, ← hh]
    exact hlaw h t hhC _ hth
  have h3 : (R : ℂ) * ((α t : ℂ) * (m : ℂ)) = (r : ℂ) * (χS x : ℂ) := by
    have := h2.symm.trans h1
    simp only [splitFacOF, MonoidHom.one_apply, inv_one, one_mul] at this
    exact mul_right_cancel₀ hℓf this
  have hu : α t * (χS x)⁻¹ = 1 := by
    apply circle_eq_one_of_pos (t := r / (R * m)) (div_pos hr (mul_pos hR hm))
    have hx0 : ((χS x : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    rw [Circle.coe_mul, Circle.coe_inv]
    push_cast
    field_simp
    linear_combination h3
  rw [← hχx χS nS hωd.resS]
  exact mul_inv_eq_one.mp hu
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceSiegelLawDiagonalLagrangianCharacter =====
