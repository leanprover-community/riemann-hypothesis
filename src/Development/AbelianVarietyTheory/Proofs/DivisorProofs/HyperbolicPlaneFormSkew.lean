import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixMulVecBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivative
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportWordMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOfIsSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementCommutesTranslates
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TracedQminorComatrixTruncatedInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeBlockConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_derivative_additive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (f : GAd σ J → ℂ), IsSm σ J f →
    ∀ (X X' : Matrix (Fin n) (Fin n) ℂ) (γ δ ε : ℝ → GAd σ J), IsLineOf σ J τ X γ → IsLineOf σ J τ X' δ →
      (IsLineOf σ J τ (X + X') ε → lineDer ε f = lineDer γ f + lineDer δ f) ∧
      (IsLineOf σ J τ (X * X' - X' * X) ε → lineDer ε f = lineDer γ (lineDer δ f) - lineDer δ (lineDer γ f)) := by
  first | exact @GlobalTheory.LeviHC.LineLie.lineDer_add_bracket | exact GlobalTheory.LeviHC.LineLie.lineDer_add_bracket | (intros; apply GlobalTheory.LeviHC.LineLie.lineDer_add_bracket <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem commutator_add_I_smul {R : Type} [Ring R] [Algebra ℂ R] (u v u' v' : R) :
    (u + Complex.I • v) * (u' + Complex.I • v') - (u' + Complex.I • v') * (u + Complex.I • v) =
      (u * u' - u' * u) + Complex.I • (u * v' - v' * u) + Complex.I • (v * u' - u' * v) - (v * v' - v' * v) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  linear_combination (norm := module) Complex.I_mul_I • (v * v' - v' * v)

theorem re_im_smul_add_I_smul {M : Type} [AddCommGroup M] [Module ℂ M] (a b : ℝ) (u v : M) :
    (a : ℂ) • u + ((-b : ℝ) : ℂ) • v + Complex.I • ((a : ℂ) • v + (b : ℂ) • u) =
      ((a : ℂ) + b * Complex.I) • (u + Complex.I • v) := by
  simp only [smul_add, add_smul, smul_smul]
  push_cast
  linear_combination (norm := module) Complex.I_mul_I • ((-(b : ℂ)) • v)

theorem exists_complexLinear_bracket_ext : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → IsUnit A.det → ∀ (B : Type) [Ring B] [Algebra ℂ B]
    (ρ : Matrix (Fin n) (Fin n) ℂ → B),
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X + X') = ρ X + ρ X') →
    (∀ (c : ℝ) X, Xᴴ * A + A * X = 0 → ρ (c • X) = (c : ℂ) • ρ X) →
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X * X' - X' * X) = ρ X * ρ X' - ρ X' * ρ X) →
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B, (∀ X X', D (X * X' - X' * X) = D X * D X' - D X' * D X) ∧
      ∀ X, Xᴴ * A + A * X = 0 → D X = ρ X := by
  intro n A hA hd B _ _ ρ hadd hr hbr
  let P : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => (1 / 2 : ℂ) • (X - adj A X)
  let Q : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun X => (-Complex.I / 2 : ℂ) • (X + adj A X)
  have hP : ∀ X, (P X)ᴴ * A + A * P X = 0 := fun X => (skew_parts hA hd X).1
  have hQ : ∀ X, (Q X)ᴴ * A + A * Q X = 0 := fun X => (skew_parts hA hd X).2.1
  have hPQ : ∀ X, X = P X + Complex.I • Q X := fun X => (skew_parts hA hd X).2.2
  have ssmul : ∀ (c : ℝ) Y, Yᴴ * A + A * Y = 0 → ((c : ℂ) • Y)ᴴ * A + A * ((c : ℂ) • Y) = 0 := by
    intro c Y h
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h,
      smul_zero]
  have sbr : ∀ Y Y', Yᴴ * A + A * Y = 0 → Y'ᴴ * A + A * Y' = 0 →
      (Y * Y' - Y' * Y)ᴴ * A + A * (Y * Y' - Y' * Y) = 0 := by
    intro Y Y' h h'
    have e : Yᴴ * A = -(A * Y) := eq_neg_of_add_eq_zero_left h
    have e' : Y'ᴴ * A = -(A * Y') := eq_neg_of_add_eq_zero_left h'
    have e1 : Y'ᴴ * Yᴴ * A = A * Y' * Y := by
      rw [Matrix.mul_assoc, e, Matrix.mul_neg, ← Matrix.mul_assoc, e', Matrix.neg_mul, neg_neg]
    have e2 : Yᴴ * Y'ᴴ * A = A * Y * Y' := by
      rw [Matrix.mul_assoc, e', Matrix.mul_neg, ← Matrix.mul_assoc, e, Matrix.neg_mul, neg_neg]
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    abel
  have hr' : ∀ (c : ℝ) Y, Yᴴ * A + A * Y = 0 → ρ ((c : ℂ) • Y) = (c : ℂ) • ρ Y := fun c Y h => by
    rw [Complex.coe_smul]; exact hr c Y h
  have adj_add : ∀ X X', adj A (X + X') = adj A X + adj A X' := fun X X' => by
    simp only [adj, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have adj_smul : ∀ (c : ℂ) X, adj A (c • X) = star c • adj A X := fun c X => by
    simp only [adj, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have Padd : ∀ X X', P (X + X') = P X + P X' := fun X X' => by
    simp only [P, adj_add]; module
  have Qadd : ∀ X X', Q (X + X') = Q X + Q X' := fun X X' => by
    simp only [Q, adj_add]; module
  have Psmul : ∀ (a b : ℝ) X, P (((a : ℂ) + b * Complex.I) • X) = (a : ℂ) • P X + ((-b : ℝ) : ℂ) • Q X := by
    intro a b X
    simp only [P, Q, adj_smul]
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring
  have Qsmul : ∀ (a b : ℝ) X, Q (((a : ℂ) + b * Complex.I) • X) = (a : ℂ) • Q X + (b : ℂ) • P X := by
    intro a b X
    simp only [P, Q, adj_smul]
    ext i j
    simp [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply]
    ring_nf; simp only [Complex.I_sq]; ring
  have skew_zero : (0 : Matrix (Fin n) (Fin n) ℂ)ᴴ * A + A * 0 = 0 := by simp
  have ρ0 : ρ 0 = 0 := by
    have := hadd 0 0 skew_zero skew_zero
    rw [add_zero] at this
    simpa using this
  have hsk : ∀ Y, Yᴴ * A + A * Y = 0 → adj A Y = -Y := fun Y h => by
    rw [adj, Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  have PY : ∀ Y, Yᴴ * A + A * Y = 0 → P Y = Y := fun Y h => by
    simp only [P, hsk Y h]; module
  have QY : ∀ Y, Yᴴ * A + A * Y = 0 → Q Y = 0 := fun Y h => by
    simp only [Q, hsk Y h, add_neg_cancel, smul_zero]
  let D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B :=
    { toFun := fun X => ρ (P X) + Complex.I • ρ (Q X)
      map_add' := fun X X' => by
        rw [Padd, Qadd, hadd _ _ (hP _) (hP _), hadd _ _ (hQ _) (hQ _), smul_add]
        abel
      map_smul' := fun c X => by
        obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, c = a + b * Complex.I := ⟨c.re, c.im, (Complex.re_add_im c).symm⟩
        simp only [RingHom.id_apply]
        rw [Psmul, Qsmul, hadd _ _ (ssmul _ _ (hP _)) (ssmul _ _ (hQ _)),
          hadd _ _ (ssmul _ _ (hQ _)) (ssmul _ _ (hP _)), hr' _ _ (hP _), hr' _ _ (hQ _), hr' _ _ (hQ _),
          hr' _ _ (hP _)]
        exact re_im_smul_add_I_smul a b _ _ }
  have hD : ∀ X, D X = ρ (P X) + Complex.I • ρ (Q X) := fun X => rfl
  have hDs : ∀ Y, Yᴴ * A + A * Y = 0 → D Y = ρ Y := fun Y h => by
    rw [hD, PY Y h, QY Y h, ρ0, smul_zero, add_zero]
  have key : ∀ p q p' q', pᴴ * A + A * p = 0 → qᴴ * A + A * q = 0 → p'ᴴ * A + A * p' = 0 →
      q'ᴴ * A + A * q' = 0 →
      D ((p + Complex.I • q) * (p' + Complex.I • q') - (p' + Complex.I • q') * (p + Complex.I • q)) =
        D (p + Complex.I • q) * D (p' + Complex.I • q') - D (p' + Complex.I • q') * D (p + Complex.I • q) := by
    intro p q p' q' hp hq hp' hq'
    rw [commutator_add_I_smul, map_sub, map_add, map_add, map_smul, map_smul, hDs _ (sbr _ _ hp hp'),
      hDs _ (sbr _ _ hp hq'), hDs _ (sbr _ _ hq hp'), hDs _ (sbr _ _ hq hq'), hbr _ _ hp hp', hbr _ _ hp hq',
      hbr _ _ hq hp', hbr _ _ hq hq', map_add, map_add, map_smul, map_smul, hDs _ hp, hDs _ hq, hDs _ hp', hDs _ hq',
      commutator_add_I_smul]
  refine ⟨D, fun X X' => ?_, hDs⟩
  have := key _ _ _ _ (hP X) (hQ X) (hP X') (hQ X')
  rwa [← hPQ X, ← hPQ X'] at this

end GlobalTheory.LeviHC
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_algebra_rep_derivation_matrix : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → IsUnit A.det → ∀ (B : Type) [Ring B] [Algebra ℂ B]
    (ρ : Matrix (Fin n) (Fin n) ℂ → B),
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X + X') = ρ X + ρ X') →
    (∀ (c : ℝ) X, Xᴴ * A + A * X = 0 → ρ (c • X) = (c : ℂ) • ρ X) →
    (∀ X X', Xᴴ * A + A * X = 0 → X'ᴴ * A + A * X' = 0 → ρ (X * X' - X' * X) = ρ X * ρ X' - ρ X' * ρ X) →
    ∃ D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B, (∀ X X', D (X * X' - X' * X) = D X * D X' - D X' * D X) ∧
      ∀ X, Xᴴ * A + A * X = 0 → D X = ρ X := by
  atlas_forward_decl GlobalTheory.LeviHC.exists_complexLinear_bracket_ext
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.PlaceComm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {w w' : InfinitePlace F} {τ : EmbOver E w} {τ' : EmbOver E w'} {Z Z' : Matrix (Fin n) (Fin n) ℂ}
  {γ δ : ℝ → GAd σ J}

theorem line_commute (hw : w ≠ w') (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ) (s t : ℝ) :
    γ s * δ t = δ t * γ s := by
  obtain ⟨y, e, -⟩ := hγ s
  obtain ⟨y', e', -⟩ := hδ t
  rw [e, e']
  exact (commute_embArch σ J y (projArch_embArch_ne σ J hw y')).eq

theorem lineDer_comm (h : IsCMExt F E σ) (hw : w ≠ w') (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ)
    {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) :
    GlobalTheory.SiegelSet.lineDer γ (GlobalTheory.SiegelSet.lineDer δ φ) = GlobalTheory.SiegelSet.lineDer δ (GlobalTheory.SiegelSet.lineDer γ φ) := by
  funext g
  have hu := GlobalTheory.UAut.CentralComm.isSmFamily_translate hφ (hγ.isRealLine h)
  have e := hu.deriv_lineDer (hδ.isRealLine h) g
  refine Eq.trans ?_ e
  simp only [GlobalTheory.SiegelSet.lineDer]
  congr 1; funext s; congr 1; funext t
  rw [mul_assoc, mul_assoc, line_commute hw hγ hδ]

theorem der_comm_lines (h : IsCMExt F E σ) (hw : w ≠ w')
    {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD : IsDer σ J τ D)
    {D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD' : IsDer σ J τ' D')
    (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ) : Commute (D Z) (D' Z') := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  simp only [Module.End.mul_apply]
  rw [hD.2 Z γ hγ, hD'.2 Z' δ hδ, hD'.2 Z' δ hδ, hD.2 Z γ hγ]
  exact lineDer_comm h hw hγ hδ f.2

end GlobalTheory.LeviHC.PlaceComm

namespace GlobalTheory.LeviHC

theorem der_comm_of_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ (w' : InfinitePlace F) (τ' : EmbOver E w') (D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)),
    IsDer σ J τ' D' → w ≠ w' → ∀ X X', D X * D' X' = D' X' * D X := by
  intro F E _ _ _ _ _ σ h n J hJ w τ D hD w' τ' D' hD' hw X X'
  obtain ⟨γ₁, γ₂, e1, e2, hX⟩ := exists_lines h hJ τ X
  obtain ⟨δ₁, δ₂, f1, f2, hX'⟩ := exists_lines h hJ τ' X'
  have c : ∀ {Z Z' : Matrix (Fin n) (Fin n) ℂ} {γ δ : ℝ → GAd σ J}, IsLineOf σ J τ Z γ → IsLineOf σ J τ' Z' δ →
      Commute (D Z) (D' Z') := fun hγ hδ => PlaceComm.der_comm_lines h hw hD hD' hγ hδ
  have key : Commute (D X) (D' X') := by
    rw [hX, hX']
    rw [map_add, map_add, LinearMap.map_smul D Complex.I _, LinearMap.map_smul D' Complex.I _]
    exact ((c e1 f1).add_right ((c e1 f2).smul_right Complex.I)).add_left
      (((c e2 f1).add_right ((c e2 f2).smul_right Complex.I)).smul_left Complex.I)
  exact key.eq

end GlobalTheory.LeviHC

end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivations_commute_distinct_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ (w' : InfinitePlace F) (τ' : EmbOver E w') (D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)),
    IsDer σ J τ' D' → w ≠ w' → ∀ X X', D X * D' X' = D' X' * D X := by
  first | exact @GlobalTheory.LeviHC.der_comm_of_ne | exact GlobalTheory.LeviHC.der_comm_of_ne | (intros; apply GlobalTheory.LeviHC.der_comm_of_ne <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem isLineOf_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∃ (w : InfinitePlace F) (Z : Matrix (Fin n) (Fin n) ℂ), IsLineOf σ J (τ w) Z γ := by
  intro F E _ _ _ _ _ σ hcm n J _hJ τ γ hγ
  obtain ⟨w, τ', Z', -, hl⟩ := hγ
  choose y hy1 hy2 using hl
  have hinj : Function.Injective (GlobalTheory.Orb.archMat σ J τ') := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J hcm, GlobalTheory.Orb.archMat_eq_archEquiv J hcm] at e
    exact (archEquiv J hcm τ').injective (Subtype.ext (Units.ext e))
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J hcm τ').continuous_iff]
    have : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ') ∘ y) = fun t i j => NormedSpace.exp (t • Z') i j := by
      funext t i j
      simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy2]
    rw [this]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z') :=
      NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply_apply i j).comp hexp
  have h0 : y 0 = 1 := hinj (by rw [hy2, map_one, zero_smul, NormedSpace.exp_zero])
  have hm : ∀ s t, y (s + t) = y s * y t := fun s t => hinj (by
    rw [hy2, map_mul, hy2, hy2, add_smul]
    exact NormedSpace.exp_add_of_commute ((Commute.refl Z').smul_left _ |>.smul_right _))
  obtain ⟨Z, hZ⟩ := GlobalTheory.OneParamMatrix.eq_exp_of_continuous_oneParameter
    (fun t => GlobalTheory.Orb.archMat σ J (τ w) (y t)) ((GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp hc)
    (by simp only [h0, map_one]) (fun s t => by simp only [hm, map_mul])
  exact ⟨w, Z, fun t => ⟨y t, hy1 t, hZ t⟩⟩

end GlobalTheory.LeviHC
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_line_is_line_of_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∃ (w : InfinitePlace F) (Z : Matrix (Fin n) (Fin n) ℂ), IsLineOf σ J (τ w) Z γ := by
  atlas_forward_decl GlobalTheory.LeviHC.isLineOf_of_isRealLine
end

section
noncomputable section

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut.DopComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem dop_eq_sum (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) :
    dop z f = ∑ l ∈ z.support, z l • l.foldr lineDer f := by
  funext g
  simp only [dop, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem isSm_sum {ι : Type} (s : Finset ι) (φ : ι → GAd σ J → ℂ) (h : ∀ i ∈ s, IsSm σ J (φ i)) :
    IsSm σ J (∑ i ∈ s, φ i) := by
  intro k γ hγ g
  simp only [Finset.sum_apply]
  exact ContDiff.sum fun i hi => h i hi k γ hγ g

theorem foldr_sum {l : List (ℝ → GAd σ J)} (hl : ∀ γ ∈ l, IsRealLine σ J γ) {ι : Type} (s : Finset ι)
    (φ : ι → GAd σ J → ℂ) (h : ∀ i ∈ s, IsSm σ J (φ i)) :
    l.foldr lineDer (∑ i ∈ s, φ i) = ∑ i ∈ s, l.foldr lineDer (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := foldr_smul l (0 : ℂ) (0 : GAd σ J → ℂ)
    simpa using this
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSm σ J (φ i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      foldr_add hl (h a (Finset.mem_insert_self _ _)) (isSm_sum s φ hs), ih hs]

theorem dop_dop {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (f : GAd σ J → ℂ) (hf : IsSm σ J f)
    (w z : List (ℝ → GAd σ J) →₀ ℂ) (hw : ∀ l ∈ w.support, ∀ γ ∈ l, IsRealLine σ J γ)
    (hz : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) :
    IsSm σ J (dop z f) ∧ dop w (dop z f) = dop (wordMul w z) f := by
  have hs : ∀ l ∈ z.support, IsSm σ J (z l • l.foldr lineDer f) :=
    fun l hl => isSm_smul _ (isSm_foldr (hz l hl) hf)
  refine ⟨by rw [dop_eq_sum]; exact isSm_sum _ _ hs, ?_⟩
  rw [dop_eq_sum w, wordMul, Finsupp.sum, dop_sum_comb]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finsupp.sum, dop_sum_comb, dop_eq_sum z, foldr_sum (hw l hl) _ _ hs, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  rw [dop_single, foldr_smul, List.foldr_append]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.UAut.DopComp

end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC.WordAlg

theorem adjoin_word : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), ∃ z : List (ℝ → GAd σ J) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧ ∀ f : SmG σ J, dop z f.1 = (u f).1 := by
  intro F E _ _ _ _ _ σ h n J hJ w τ D hD u hu
  classical
  induction hu using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨X, rfl⟩ := hx
    obtain ⟨γ₁, γ₂, e1, e2, e3⟩ := exists_lines h hJ τ X
    generalize (1 / 2 : ℂ) • (X - adj (J.map τ.1) X) = X₁ at e1 e3
    generalize (-Complex.I / 2 : ℂ) • (X + adj (J.map τ.1) X) = X₂ at e2 e3
    have hX : D X = D X₁ + Complex.I • D X₂ := by rw [← map_smul, ← map_add, ← e3]
    refine ⟨Finsupp.single [γ₁] 1 + Finsupp.single [γ₂] Complex.I, fun l hl γ hγ => ?_, fun f => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl <;>
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl) <;>
        obtain rfl := List.mem_singleton.1 hγ
      exacts [e1.isRealLine h, e2.isRealLine h]
    · rw [dop_add_comb, dop_single, dop_single]
      rw [hX, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul, hD.2 _ _ e1 f,
        hD.2 _ _ e2 f]
      funext g
      simp
  | algebraMap c =>
    refine ⟨Finsupp.single [] c, fun l hl γ hγ => ?_, fun f => ?_⟩
    · obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hl)
      simp at hγ
    rw [dop_single]
    funext g
    simp [Algebra.algebraMap_eq_smul_one]
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, ez⟩ := hx
    obtain ⟨z', hz', ez'⟩ := hy
    refine ⟨z + z', fun l hl γ hγ => ?_, fun f => ?_⟩
    · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl
      exacts [hz l hl γ hγ, hz' l hl γ hγ]
    · rw [dop_add_comb, ez, ez', LinearMap.add_apply, Submodule.coe_add]
  | mul x y _ _ hx hy =>
    obtain ⟨z, hz, ez⟩ := hx
    obtain ⟨z', hz', ez'⟩ := hy
    refine ⟨wordMul z z', fun m hm γ hγ => ?_, fun f => ?_⟩
    · obtain ⟨l, hl, l', hl', rfl⟩ := mem_support_wordMul hm
      rcases List.mem_append.1 hγ with h' | h'
      exacts [hz l hl γ h', hz' l' hl' γ h']
    · obtain ⟨-, h2⟩ := GlobalTheory.UAut.DopComp.dop_dop σ J f.1 f.2 z z' hz hz'
      rw [← h2, ez', ez (y f), Module.End.mul_apply]

end GlobalTheory.LeviHC.WordAlg
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_enveloping_line_derivatives : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ u ∈ Algebra.adjoin ℂ (Set.range D), ∃ z : List (ℝ → GAd σ J) →₀ ℂ,
      (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) ∧ ∀ f : SmG σ J, dop z f.1 = (u f).1 := by
  atlas_forward_decl GlobalTheory.LeviHC.WordAlg.adjoin_word
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.CapelliGelfand

open Formalism.REAL Finset

theorem epow_eq_pow {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (m : ℕ) (a b : Fin n) :
    epow E m a b = (Matrix.of E ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp [epow, pow_succ, Matrix.mul_apply, ih]

theorem etr_succ_eq_gelfA {B : Type} [Ring B] {n : ℕ} (E : Fin n → Fin n → B) (k : ℕ) :
    etr E (k + 1) = GlobalTheory.SmoothForms.gelfA E k := by
  rw [GlobalTheory.SmoothForms.gelfA_eq_sum_pow]; simp [etr, epow_eq_pow]

theorem etr_mem_adjoin_qdet (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (N : ℕ) : etr X N ∈ Algebra.adjoin ℂ (Set.range (qdet X)) := by
  set S := Algebra.adjoin ℂ (Set.range (qdet X)) with hS
  have hq : ∀ u, qdet X u ∈ S := fun u => Algebra.subset_adjoin ⟨u, rfl⟩
  cases n with
  | zero => simp [etr]
  | succ m =>
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet A (m + 1) X
      have hmin : ∀ i j : Fin (m + 1), ∃ c' : ℕ → A, ∀ w : ℂ,
          qminor X (Fin.succAbove j) (Fin.succAbove i) w = ∑ d ∈ range (m + 1), w ^ d • c' d := by
        intro i j
        obtain ⟨c', hc'⟩ := GlobalTheory.qminor_polyMap A (m + 1) m X (Fin.succAbove j) (Fin.succAbove i) 0
        exact ⟨c', fun w => by simpa using hc' w⟩
      choose cm hcm using hmin
      let Rs : ℂ → A := fun w => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * qminor X (Fin.succAbove j) (Fin.succAbove i) w
          * epow X (N + 1) j i
      let Rc : ℕ → A := fun d => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ)) : ℤ) : A) * cm i j d * epow X (N + 1) j i
      have hR : ∀ w : ℂ, Rs w = ∑ d ∈ range (m + 1), w ^ d • Rc d := by
        intro w
        simp only [Rs, Rc, hcm, mul_sum, sum_mul, smul_sum, mul_smul_comm, smul_mul_assoc]
        conv_lhs => enter [2, x]; rw [sum_comm]
        rw [sum_comm]
      let f : ℂ → A := fun u => qdet X u * etr X N - Rs u
      let a : ℕ → A := fun i => c i * etr X N - if i < m + 1 then Rc i else 0
      have hf : ∀ u, f u = ∑ i ∈ range (m + 1 + 1), u ^ i • a i := by
        intro u
        simp only [f, a, hc u, hR u, sum_mul, smul_mul_assoc, smul_sub, sum_sub_distrib]
        congr 1
        rw [sum_range_succ _ (m + 1), if_neg (lt_irrefl _), smul_zero, add_zero]
        exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
      have hmem : ∀ u, f u ∈ S := by
        intro u
        have h1 := GlobalTheory.T.traced_qminor_comatrix_truncated_inverse A m X hX u N
        rw [← GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor', sum_range_succ, Nat.sub_self, pow_zero, mul_one, mul_add] at h1
        have key : algebraMap ℂ A ((-1) ^ N) * f u = algebraMap ℂ A ((u - m) ^ (N + 1)) * (qdet X (u + 1) - qdet X u)
            - qdet X u * ∑ k ∈ range N, algebraMap ℂ A ((-1) ^ k * (u - m) ^ (N - k)) * etr X k := by
          simp only [f]
          rw [mul_sub, ← mul_assoc, Algebra.commutes, mul_assoc, sub_eq_sub_iff_add_eq_add, h1]
          abel
        have hm : algebraMap ℂ A ((-1) ^ N) * f u ∈ S := by
          rw [key]
          refine sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (sub_mem (hq _) (hq _)))
            (mul_mem (hq _) (sum_mem fun k hk => mul_mem (Subalgebra.algebraMap_mem _ _) (ih k (mem_range.mp hk))))
        have : f u = algebraMap ℂ A ((-1) ^ N) * (algebraMap ℂ A ((-1) ^ N) * f u) := by
          rw [← mul_assoc, ← map_mul, ← mul_pow, neg_one_mul, neg_neg, one_pow, map_one, one_mul]
        rw [this]
        exact mul_mem (Subalgebra.algebraMap_mem _ _) hm
      have htop := GlobalTheory.LeviHC.coeff_mem_span hf (i := m + 1) (Nat.lt_succ_self _)
      have ha : a (m + 1) = etr X N := by simp [a, hc1]
      rw [ha] at htop
      have hle : Submodule.span ℂ (Set.range f) ≤ Subalgebra.toSubmodule S :=
        Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact hmem u)
      exact hle htop

theorem gelfA_mem_adjoin_qdet : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X)) := by
  intro A _ _ n X hX k
  rw [← etr_succ_eq_gelfA]
  exact etr_mem_adjoin_qdet A n X hX (k + 1)

end GlobalTheory.CapelliGelfand
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_generator_mem_quantum_det : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X →
    ∀ k : ℕ, GlobalTheory.SmoothForms.gelfA X k ∈ Algebra.adjoin ℂ (Set.range (Formalism.REAL.qdet X)) := by
  atlas_forward_decl GlobalTheory.CapelliGelfand.gelfA_mem_adjoin_qdet
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC.MultiCentre

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def genSet (E : Fin n → Fin n → A) : Set A := Set.range fun p : Fin n × Fin n => E p.1 p.2

theorem gelfA_mem_adjoin (E : Fin n → Fin n → A) (k : ℕ) :
    GlobalTheory.SmoothForms.gelfA E k ∈ Algebra.adjoin ℂ (genSet E) := by
  unfold GlobalTheory.SmoothForms.gelfA
  refine Subalgebra.sum_mem _ fun idx _ => Subalgebra.list_prod_mem _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨a, rfl⟩ := hx
  exact Algebra.subset_adjoin ⟨(_, _), rfl⟩

theorem adjoin_le_centralizer {S T : Set A} (h : ∀ x ∈ S, ∀ y ∈ T, y * x = x * y) :
    Algebra.adjoin ℂ S ≤ Subalgebra.centralizer ℂ T :=
  Algebra.adjoin_le fun x hx => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => h x hx y hy

theorem centre_of_commuting_families_sup (hRC : RelativeCentre) {ι : Type} (X : ι → Fin n → Fin n → A)
    (hX : ∀ i, Formalism.REAL.GlRel (X i)) (hc : ∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b)
    (s : Finset ι) : ∀ C : Subalgebra ℂ A, (∀ i ∈ s, C ≤ Subalgebra.centralizer ℂ (genSet (X i))) →
      ∀ z ∈ s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C,
        (∀ i ∈ s, z ∈ Subalgebra.centralizer ℂ (genSet (X i))) →
        z ∈ s.sup (fun i => Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA (X i)))) ⊔ C := by
  classical
  induction s using Finset.induction_on with
  | empty => intro C _ z hz _; simpa using hz
  | insert w s hw ih =>
    intro C hC z hz hzc
    rw [Finset.sup_insert] at hz ⊢
    have hle : s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C ≤ Subalgebra.centralizer ℂ (genSet (X w)) := by
      refine sup_le (Finset.sup_le fun i hi => adjoin_le_centralizer ?_) (hC w (Finset.mem_insert_self _ _))
      rintro x ⟨⟨a, b⟩, rfl⟩ y ⟨⟨c, d⟩, rfl⟩
      exact hc w i (fun h => hw (h ▸ hi)) c d a b
    have hB : ∀ b ∈ s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C, ∀ a c, X w a c * b = b * X w a c :=
      fun b hb a c => (Subalgebra.mem_centralizer_iff ℂ).1 (hle hb) _ ⟨(a, c), rfl⟩
    have hz' : z ∈ Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => X w p.1 p.2) ⊔
        (s.sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ C) := by
      rw [← sup_assoc]; exact hz
    have h1 := hRC A n (X w) (hX w) _ hB z hz' fun a c =>
      (Subalgebra.mem_centralizer_iff ℂ).1 (hzc w (Finset.mem_insert_self _ _)) _ ⟨(a, c), rfl⟩
    rw [sup_left_comm] at h1
    have hC' : ∀ i ∈ s, Algebra.adjoin ℂ (Set.range (GlobalTheory.SmoothForms.gelfA (X w))) ⊔ C ≤
        Subalgebra.centralizer ℂ (genSet (X i)) := by
      intro i hi
      refine sup_le ((Algebra.adjoin_le (Set.range_subset_iff.2 fun k => gelfA_mem_adjoin (X w) k)).trans
        (adjoin_le_centralizer ?_)) (hC i (Finset.mem_insert_of_mem hi))
      rintro x ⟨⟨a, b⟩, rfl⟩ y ⟨⟨c, d⟩, rfl⟩
      exact hc i w (fun h => hw (h ▸ hi)) c d a b
    have h2 := ih _ hC' z h1 fun i hi => hzc i (Finset.mem_insert_of_mem hi)
    rw [sup_assoc]; rwa [sup_left_comm] at h2

theorem centre_multi : RelativeCentre → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Finite ι] (n : ℕ)
    (X : ι → Fin n → Fin n → A),
    (∀ i, Formalism.REAL.GlRel (X i)) → (∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × Fin n × Fin n => X p.1 p.2.1 p.2.2),
      (∀ i a b, X i a b * z = z * X i a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × ℕ => GlobalTheory.SmoothForms.gelfA (X p.1) p.2) := by
  intro hRC A _ _ ι _ n X hX hc z hz hzc
  classical
  letI := Fintype.ofFinite ι
  have hz' : z ∈ (Finset.univ : Finset ι).sup (fun i => Algebra.adjoin ℂ (genSet (X i))) ⊔ ⊥ := by
    rw [sup_bot_eq]
    refine (Algebra.adjoin_le ?_) hz
    rintro _ ⟨⟨i, a, b⟩, rfl⟩
    exact Finset.le_sup (f := fun i => Algebra.adjoin ℂ (genSet (X i))) (Finset.mem_univ i)
      (Algebra.subset_adjoin ⟨(a, b), rfl⟩)
  have h := centre_of_commuting_families_sup hRC X hX hc Finset.univ ⊥ (fun _ _ => bot_le) z hz' fun i _ =>
    (Subalgebra.mem_centralizer_iff ℂ).2 (by rintro _ ⟨⟨a, b⟩, rfl⟩; exact hzc i a b)
  rw [sup_bot_eq] at h
  refine (Finset.sup_le fun i _ => Algebra.adjoin_mono ?_) h
  rintro _ ⟨k, rfl⟩
  exact ⟨(i, k), rfl⟩

end GlobalTheory.LeviHC.MultiCentre
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centre_generated_by_gelfand : RelativeCentre → ∀ (A : Type) [Ring A] [Algebra ℂ A] (ι : Type) [Finite ι] (n : ℕ) (X : ι → Fin n → Fin n → A),
    (∀ i, Formalism.REAL.GlRel (X i)) → (∀ i j, i ≠ j → ∀ a b c d, X i a b * X j c d = X j c d * X i a b) →
    ∀ z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × Fin n × Fin n => X p.1 p.2.1 p.2.2),
      (∀ i a b, X i a b * z = z * X i a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun p : ι × ℕ => GlobalTheory.SmoothForms.gelfA (X p.1) p.2) := by
  atlas_forward_decl GlobalTheory.LeviHC.MultiCentre.centre_multi
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.FrameInv

open Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_entry (σ : E →ₐ[F] E) {N : ℕ} {ι₁ ι₂ : Type*} (J : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) ι₁ E)
    (B : Matrix (Fin N) ι₂ E) (i : ι₁) (j : ι₂) :
    (Aᵀ * J * B.map σ) i j = form σ J (fun r => A r i) (fun r => B r j) := by
  simp only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) (a b : Fin N → E) :
    form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsk]; ring

def idx (n₁ : ℕ) : Fin (1 + n₁ + 1) → Fin n₁ ⊕ Fin 2 :=
  Fin.addCases (Fin.addCases (fun _ => Sum.inr 0) fun k => Sum.inl k) fun _ => Sum.inr 1

theorem one_idx {n₁ : ℕ} (i j : Fin (1 + n₁ + 1)) :
    (1 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E) (idx n₁ i) (idx n₁ j) = (1 : Matrix _ _ E) i j := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
        | right k => simp [idx, one_apply, Fin.ext_iff] <;> omega
      | right b => simp [idx, one_apply, Fin.ext_iff] <;> omega
    | right k =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left b => simp [idx, one_apply, Fin.ext_iff] <;> omega
        | right l => simp [idx, one_apply, Fin.ext_iff]
      | right b => simp [idx, one_apply, Fin.ext_iff] <;> omega
  | right a =>
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left b => simp [idx, one_apply, Fin.ext_iff] <;> omega
      | right l => simp [idx, one_apply, Fin.ext_iff] <;> omega
    | right b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]

variable [NumberField F] [NumberField E]

theorem frame_invertible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 ∧ R * frame H = 1 := by
  intro F E _ _ _ _ _ σ hcm n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet
  have hσ : ∀ e, σ (σ e) = e := GlobalTheory.SiegelSet.sigma_sigma hcm
  subst hn
  set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY
  set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ
  set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0] with hS₂
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap hσ hsk, hxy, map_one]
  have horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0 := by
    intro i
    have e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1 := by
      funext r; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e]; exact horth _
  have hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [fromBlocks_apply₁₁, ← hgram, gram_entry, gram_entry]; rfl
    · rw [fromBlocks_apply₁₂, gram_entry]
      fin_cases j
      · simpa [Q, XY] using (horth' i).1
      · simpa [Q, XY] using (horth' i).2
    · rw [fromBlocks_apply₂₁, gram_entry, form_swap hσ hsk]
      fin_cases i
      · simp [Q, XY, (horth' j).1]
      · simp [Q, XY, (horth' j).2]
    · rw [fromBlocks_apply₂₂, gram_entry]
      fin_cases i <;> fin_cases j <;> simp [Q, XY, S₂, hxx, hyy, hxy, hyx]
  have hdetK : (fromBlocks Y₁.J 0 0 S₂).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]; simp [S₂, Matrix.det_fin_two_of, hdet]
  have hKu : IsUnit (fromBlocks Y₁.J 0 0 S₂).det := isUnit_iff_ne_zero.2 hdetK
  set R' : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map σ with hR'
  have h0 : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = 1 := by
    have : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = (fromBlocks Y₁.J 0 0 S₂)⁻¹ * (Qᵀ * Y.J * Q.map σ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hK, nonsing_inv_mul _ hKu]
  have hQQ : (Q.map σ).map (σ : E →+* E) = Q := by ext i j; simp [hσ]
  have hRQ : R' * Q = 1 := by
    calc R' * Q = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map (σ : E →+* E) * (Q.map σ).map (σ : E →+* E) := by
          rw [hQQ]; rfl
      _ = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ).map (σ : E →+* E) := Matrix.map_mul.symm
      _ = 1 := by rw [h0]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hfr : ∀ r c, frame H r c = Q r (idx n₁ c) := by
    intro r c
    induction c using Fin.addCases with
    | left c =>
      induction c using Fin.addCases with
      | left a => simp [frame, idx, Q, XY]
      | right k => simp [frame, idx, Q, XY]
    | right a => simp [frame, idx, Q, XY]
  refine ⟨Matrix.of fun i r => R' (idx n₁ i) r, ?_, ?_⟩
  · refine (mul_eq_one_comm_of_card_eq (Fin (n₁ + 2)) (Fin (1 + n₁ + 1)) E (by simp; omega)).2 ?_
    ext i j
    simp only [mul_apply, of_apply, hfr]
    rw [← one_idx (E := E) i j, ← hRQ, mul_apply]
  · ext i j
    simp only [mul_apply, of_apply, hfr]
    rw [← one_idx (E := E) i j, ← hRQ, mul_apply]

end GlobalTheory.LeviHC.FrameInv

end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_hyperbolic_first : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 ∧ R * frame H = 1 := by
  atlas_forward_decl GlobalTheory.LeviHC.FrameInv.frame_invertible
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open Matrix

theorem blk_le_two (n₁ : ℕ) (i : Fin (1 + n₁ + 1)) : blk n₁ i ≤ 2 := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => simp [blk]
    | right k => simp [blk]
  | right a => simp [blk]

theorem blk_cases {n₁ : ℕ} (i : Fin (1 + n₁ + 1)) :
    (∃ a, i = Fin.castAdd 1 (Fin.castAdd n₁ a)) ∨ (∃ k, i = mid k) ∨ (∃ a, i = Fin.natAdd (1 + n₁) a) := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => exact Or.inl ⟨a, rfl⟩
    | right k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | right a => exact Or.inr (Or.inr ⟨a, rfl⟩)

theorem one_sub_four_mul_ne_zero {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hab : a + b ≠ 2) :
    (1 - 4 * (2⁻¹ : ℂ) ^ (a + b)) ≠ 0 := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | norm_num

theorem blk_support_of_mul_eq_one {n₁ : ℕ} {M N : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ}
    (hM : ∀ i j, blk n₁ i + blk n₁ j ≠ 2 → M i j = 0) (hMN : M * N = 1) :
    ∀ i j, blk n₁ i + blk n₁ j ≠ 2 → N i j = 0 := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ, D = diagonal fun i => (2 : ℂ) ^ blk n₁ i :=
    ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ, D = diagonal fun i => (2⁻¹ : ℂ) ^ blk n₁ i :=
    ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; rw [← mul_pow]; norm_num
  have hMDi : M * Di = (4⁻¹ : ℂ) • (D * M) := by
    ext i j
    rw [hD, hDi, mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul]
    by_cases h : blk n₁ i + blk n₁ j = 2
    · have e : (2 : ℂ) ^ blk n₁ i = 4 * 2⁻¹ ^ blk n₁ j := by
        have : (2 : ℂ) ^ blk n₁ i * 2 ^ blk n₁ j = 4 := by rw [← pow_add, h]; norm_num
        rw [← this, mul_assoc, ← mul_pow]; norm_num
      rw [e]; ring
    · rw [hM i j h]; ring
  have hNM : N * M = 1 := mul_eq_one_comm.1 hMN
  have h1 : M * ((4 : ℂ) • (Di * N * Di)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMDi, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc D M N, hMN, Matrix.mul_one, hDDi]
    norm_num
  have key : N = (4 : ℂ) • (Di * N * Di) := by
    calc N = N * (M * ((4 : ℂ) • (Di * N * Di))) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
  intro i j hij
  have e := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, hDi, mul_diagonal, diagonal_mul, smul_eq_mul] at e
  have h0 : (1 - 4 * (2⁻¹ : ℂ) ^ (blk n₁ i + blk n₁ j)) * N i j = 0 := by
    rw [pow_add]; linear_combination e
  exact (mul_eq_zero.1 h0).resolve_left (one_sub_four_mul_ne_zero (blk_le_two n₁ i) (blk_le_two n₁ j) hij)

theorem adj_frame_blockTri : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∀ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 → R * frame H = 1 →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∀ (τ : E →+* ℂ) (s : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
      (∀ i j, blk n₁ j < blk n₁ i + s → (R.map τ * X * (frame H).map τ) i j = 0) →
      ∀ i j, blk n₁ j < blk n₁ i + s → (R.map τ * adj ((c • Y.J.map σ).map τ) X * (frame H).map τ) i j = 0 := by
  intro F E _ _ _ _ _ σ h n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet1 R hQR hRQ c hc hA hA₁ τ s X hX i j hij
  have hσ : ∀ e, σ (σ e) = e := fun e => τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have hQR' : (frame H).map τ * R.map τ = 1 := by
    rw [← Matrix.map_mul, hQR, Matrix.map_one _ τ.map_zero τ.map_one]
  have hRQ' : R.map τ * (frame H).map τ = 1 := by
    rw [← Matrix.map_mul, hRQ, Matrix.map_one _ τ.map_zero τ.map_one]
  have hAu : IsUnit ((c • Y.J.map σ).map τ).det := isUnit_det_map hA τ

  have hGf : ∀ a b, ((frame H)ᵀ * Y.J * (frame H).map σ) a b =
      form σ Y.J (fun r => frame H r a) (fun r => frame H r b) := by
    intro a b
    simp only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    exact Finset.sum_comm
  have hskew : ∀ u v : Fin n → E, form σ Y.J u v = -σ (form σ Y.J v u) := by
    intro u v
    simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsk]; ring
  have hcol : ∀ k : Fin n₁, (fun r => H.ι r k) = H.ι *ᵥ Pi.single k 1 := by
    intro k; ext r; simp [mulVec, dotProduct, Pi.single_apply]
  have hGs : ∀ a b, blk n₁ a + blk n₁ b ≠ 2 → ((frame H)ᵀ * Y.J * (frame H).map σ) a b = 0 := by
    intro a b hab
    rw [hGf]
    rcases blk_cases a with ⟨a, rfl⟩ | ⟨k, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases blk_cases b with ⟨b, rfl⟩ | ⟨l, rfl⟩ | ⟨b, rfl⟩ <;>
      simp only [block_matrix_mulVec_basis, blk_mid, blk_y, frame_alt, frame_mid, frame_y] at hab ⊢
    · exact hxx
    · rw [hcol, hskew, (horth _).1, map_zero, neg_zero]
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).1
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).2
    · exact absurd rfl hab
    · rw [hcol, hskew, (horth _).2, map_zero, neg_zero]
    · exact hyy

  have hA'e : ∀ a b, (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) a b =
      τ c * star (τ (((frame H)ᵀ * Y.J * (frame H).map σ) a b)) := by
    intro a b
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      transpose_apply, map_mul, map_sum, h.2.2.2, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hA's : ∀ a b, blk n₁ a + blk n₁ b ≠ 2 →
      (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) a b = 0 := by
    intro a b hab
    rw [hA'e, hGs a b hab, map_zero, star_zero, mul_zero]
  have hAB : (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) *
      (R.map τ * ((c • Y.J.map σ).map τ)⁻¹ * (R.map τ)ᴴ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((frame H).map τ) (R.map τ), hQR', Matrix.one_mul,
      ← Matrix.mul_assoc ((c • Y.J.map σ).map τ), Matrix.mul_nonsing_inv _ hAu, Matrix.one_mul, ← conjTranspose_mul,
      hRQ', conjTranspose_one]
  have hB's := blk_support_of_mul_eq_one hA's hAB
  have hcancel : ∀ {p : Type} (M : Matrix (Fin n) p ℂ), (R.map τ)ᴴ * (((frame H).map τ)ᴴ * M) = M := by
    intro p M
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hQR', conjTranspose_one, Matrix.one_mul]
  have hid : R.map τ * adj ((c • Y.J.map σ).map τ) X * (frame H).map τ =
      (R.map τ * ((c • Y.J.map σ).map τ)⁻¹ * (R.map τ)ᴴ) * (R.map τ * X * (frame H).map τ)ᴴ *
        (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) := by
    simp only [adj, conjTranspose_mul, Matrix.mul_assoc, hcancel]
  rw [hid, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : blk n₁ i + blk n₁ k = 2
  · by_cases h2 : blk n₁ l + blk n₁ j = 2
    · rw [conjTranspose_apply, hX l k (by omega), star_zero, mul_zero, zero_mul]
    · rw [hA's l j h2, mul_zero]
  · rw [hB's i k h1, zero_mul, zero_mul]

end GlobalTheory.LeviHC
end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.UnipFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_mul' {l m k : ℕ} (A : Matrix (Fin l) (Fin m) E) (B : Matrix (Fin m) (Fin k) E) :
    incM F (A * B) = incM F A * incM F B := by
  unfold incM
  exact Matrix.map_mul (f := (inclR (F := F) (E := E) (AF F) : E →+* AE F E))

theorem incM_one' {m : ℕ} : incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := by
  unfold incM
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mem_unip_of_strictBlockTri : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (H : Plane E n n₁) (R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E), frame H * R = 1 → R * frame H = 1 →
    ∀ u : UA σ Y.J, (∀ i j, blk n₁ j < blk n₁ i + 1 → (incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
        Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) →
      u ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y H R hQR hRQ u hW
  set Wm : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E) :=
    incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) with hWm
  have hQ : incM F (frame H) * incM F R = 1 := by rw [← incM_mul', hQR, incM_one']
  have key : (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) = incM F (frame H) * Wm := by
    rw [hWm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
  have hmv : ∀ v, mat u *ᵥ (incM F (frame H) *ᵥ v) = incM F (frame H) *ᵥ v + incM F (frame H) *ᵥ (Wm *ᵥ v) := by
    intro v
    have e : mat u = 1 + (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) := by abel
    rw [e, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  set x0 : Fin (1 + n₁ + 1) := Fin.castAdd 1 (Fin.castAdd n₁ 0) with hx0
  have hx : incV F H.x = incM F (frame H) *ᵥ Pi.single x0 1 := by
    ext r
    rw [Matrix.mulVec_single]
    simp [incV, incM, hx0, frame_alt]
  have hWx : Wm *ᵥ Pi.single x0 1 = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.zero_apply]
    apply hW
    rw [hx0, block_matrix_mulVec_basis]
    omega
  apply Subgroup.subset_closure
  refine ⟨?_, fun z => ⟨∑ k, Wm x0 (mid k) * z k, ?_⟩⟩
  · rw [hx, hmv, hWx, Matrix.mulVec_zero, add_zero]
  · let vz : Fin (1 + n₁ + 1) → AE F E := Fin.addCases (Fin.addCases (fun _ => 0) fun k => z k) fun _ => 0
    have hι : incM F H.ι *ᵥ z = incM F (frame H) *ᵥ vz := by
      ext r
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero,
        Finset.sum_const_zero, zero_add, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [incM, frame]
    have hWz : Wm *ᵥ vz = (∑ k, Wm x0 (mid k) * z k) • Pi.single x0 1 := by
      have hs : ∀ i, (Wm *ᵥ vz) i = ∑ k, Wm i (mid k) * z k := by
        intro i
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, vz, Fin.addCases_left, Fin.addCases_right, mul_zero,
          Finset.sum_const_zero, zero_add, add_zero]
        rfl
      ext i
      rw [hs]
      induction i using Fin.addCases with
      | left i =>
        induction i using Fin.addCases with
        | left a =>
          have ha : a = 0 := Subsingleton.elim _ _
          subst ha
          simp [hx0]
        | right k' =>
          have hne : (Fin.castAdd 1 (Fin.natAdd 1 k') : Fin (1 + n₁ + 1)) ≠ x0 := by
            rw [hx0]; intro h; have := congrArg Fin.val h; simp at this
          rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [hW, zero_mul]
          show blk n₁ (mid k) < blk n₁ (mid k') + 1
          rw [blk_mid, blk_mid]
          omega
      | right a =>
        have hne : (Fin.natAdd (1 + n₁) a : Fin (1 + n₁ + 1)) ≠ x0 := by
          rw [hx0]; intro h; have := congrArg Fin.val h; (simp at this) <;> omega
        rw [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hW, zero_mul]
        rw [blk_mid, blk_y]
        omega
    rw [hι, hmv, hWz, Matrix.mulVec_smul, ← hx]

end GlobalTheory.LeviHC.UnipFrame
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_block_triangular_nilpotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (H : Plane E n n₁) (R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E), frame H * R = 1 → R * frame H = 1 →
    ∀ u : UA σ Y.J, (∀ i j, blk n₁ j < blk n₁ i + 1 → (incM F R * (mat u - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
        Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) →
      u ∈ unip σ Y H := by
  atlas_forward_decl GlobalTheory.LeviHC.UnipFrame.mem_unip_of_strictBlockTri
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

noncomputable section

namespace GlobalTheory.ThK.UnipClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Set (UA σ W.J) :=
  {u | mat u *ᵥ incV F H'.x = incV F H'.x ∧
    ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}

theorem mat_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) :
    mat (g * h) = mat g * mat h := rfl

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  show ((g⁻¹ : UA σ J).1.1) * g.1.1 = 1
  rw [← Units.val_mul]
  show (((g⁻¹ * g : UA σ J) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
  simp

theorem mat_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} :
    mat (1 : UA σ J) = 1 := rfl

def carrierSub (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := carrierSet σ W H'
  one_mem' := ⟨by rw [mat_one, Matrix.one_mulVec], fun z => ⟨0, by rw [mat_one, Matrix.one_mulVec, zero_smul, add_zero]⟩⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by rw [mat_mul, ← Matrix.mulVec_mulVec, hv1, hu1], fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    obtain ⟨b, hb⟩ := hv2 z
    refine ⟨a + b, ?_⟩
    rw [mat_mul, ← Matrix.mulVec_mulVec, hb, Matrix.mulVec_add, ha, Matrix.mulVec_smul, hu1, add_smul, add_assoc]
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu1]
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu2 z
    refine ⟨-a, ?_⟩
    have h1 : mat u⁻¹ *ᵥ (mat u *ᵥ (incM F H'.ι *ᵥ z)) = incM F H'.ι *ᵥ z := by
      rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx] at h1
    rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h1

theorem unip_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    unip σ W H' = carrierSub σ W H' := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun u hu => hu
  · intro u hu
    exact Subgroup.subset_closure hu

section Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)]

theorem isClosed_line {d : ℕ} (x : Fin d → E) : IsClosed {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} := by
  by_cases hx : x = 0
  · have : {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} = {0} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      have h0 : incV F x = 0 := by
        funext i
        simp [incV, hx]
      simp [h0]
    rw [this]
    exact isClosed_singleton
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    have hinv : incV F x i * inclR (F := F) (AF F) (x i)⁻¹ = 1 := by
      simp only [incV, ← map_mul, mul_inv_cancel₀ hi, map_one]
    have : {w : Fin d → AE F E | ∃ a : AE F E, w = a • incV F x} =
        {w | w = (w i * inclR (F := F) (AF F) (x i)⁻¹) • incV F x} := by
      ext w
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨a, rfl⟩
        congr 1
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hinv, mul_one]
      · intro h
        exact ⟨_, h⟩
    rw [this]
    exact isClosed_eq continuous_id
      (((continuous_apply i).mul continuous_const).smul continuous_const)

end Top

variable [T2Space (AE F E)] [IsTopologicalRing (AE F E)] in
theorem isClosed_carrierSet (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) :
    IsClosed (carrierSet σ W H') := by
  have hm : Continuous fun u : UA σ W.J => mat u := Units.continuous_val.comp continuous_subtype_val
  have h1 : IsClosed {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} :=
    isClosed_eq (hm.matrix_mulVec continuous_const) continuous_const
  have h2 : ∀ z : Fin d₁ → AE F E, IsClosed {u : UA σ W.J | ∃ a : AE F E,
      mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    intro z
    have : {u : UA σ W.J | ∃ a : AE F E, mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} =
        (fun u : UA σ W.J => mat u *ᵥ (incM F H'.ι *ᵥ z) - incM F H'.ι *ᵥ z) ⁻¹'
          {w | ∃ a : AE F E, w = a • incV F H'.x} := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_preimage, sub_eq_iff_eq_add']
    rw [this]
    exact (isClosed_line H'.x).preimage ((hm.matrix_mulVec continuous_const).sub continuous_const)
  have : carrierSet σ W H' = {u : UA σ W.J | mat u *ᵥ incV F H'.x = incV F H'.x} ∩
      ⋂ z : Fin d₁ → AE F E, {u : UA σ W.J | ∃ a : AE F E,
        mat u *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x} := by
    ext u
    simp [carrierSet]
  rw [this]
  exact h1.inter (isClosed_iInter h2)

theorem isClosed_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), IsClosed ((unip σ W H' : Subgroup (UA σ W.J)) : Set (UA σ W.J)) := by
  intro F E _ _ _ _ _ σ d d₁ W H'
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  rw [unip_eq]
  exact isClosed_carrierSet σ W H'

end GlobalTheory.ThK.UnipClosed
end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem levi_conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ Y₁.J) (m : UA σ Y.J),
    IsLevi (W₁ := Y₁) H 1 h₁ m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H h₁ m hm
  obtain ⟨hx, -, hι⟩ := hm
  have hx' : mat m *ᵥ incV F H.x = incV F H.x := by simpa using hx
  have hxi : mat m⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx']
    rw [Matrix.mulVec_mulVec, FlagPar.mat_inv_mul, Matrix.one_mulVec]
  have hh : mat h₁ * mat h₁⁻¹ = 1 := by rw [← FlagPar.mat_mul, mul_inv_cancel, FlagPar.mat_one]
  have hιi : mat m⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by
          rw [Matrix.mul_assoc (mat m⁻¹), Matrix.mul_assoc (incM F H.ι), hh, Matrix.mul_one]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← hι, ← Matrix.mul_assoc, FlagPar.mat_inv_mul, Matrix.one_mul]
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨h1, h2⟩ := hu
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ?_⟩
    · rw [FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, h1, hx']
    · obtain ⟨a, ha⟩ := h2 (mat h₁⁻¹ *ᵥ z)
      refine ⟨a, ?_⟩
      have e1 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, hιi, ← Matrix.mulVec_mulVec]
      have e2 : mat m *ᵥ (incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)) = incM F H.ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat h₁), hh, Matrix.one_mulVec]
      rw [FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add,
        Matrix.mulVec_smul, hx', e2]
  | one => simp
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := inv_mem hx
    simpa [mul_assoc] using this

end GlobalTheory.LeviHC
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_bis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ Y₁.J) (m : UA σ Y.J),
    IsLevi (W₁ := Y₁) H 1 h₁ m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H := by
  atlas_forward_decl GlobalTheory.LeviHC.levi_conj_mem_unip
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.QuotMonic

variable {M : Type} [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M)

def stabAlg : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {f | ∀ x ∈ M', f x ∈ M' ∧ (x ∈ K → f x ∈ K)}
  mul_mem' := fun {f g} hf hg x hx => ⟨(hf _ (hg x hx).1).1, fun hk => (hf _ (hg x hx).1).2 ((hg x hx).2 hk)⟩
  add_mem' := fun {f g} hf hg x hx => ⟨M'.add_mem (hf x hx).1 (hg x hx).1, fun hk => K.add_mem ((hf x hx).2 hk) ((hg x hx).2 hk)⟩
  algebraMap_mem' := fun r x hx => ⟨by simpa [Module.algebraMap_end_apply] using M'.smul_mem r hx,
    fun hk => by simpa [Module.algebraMap_end_apply] using K.smul_mem r hk⟩

variable {M' K}

def restrictQ (f : stabAlg M' K) : Module.End ℂ (M' ⧸ K.comap M'.subtype) :=
  (K.comap M'.subtype).mapQ (K.comap M'.subtype) (f.1.restrict fun x hx => (f.2 x hx).1) fun x hx => by
    simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.restrict_apply] at hx ⊢
    exact (f.2 x x.2).2 hx

variable (M' K) in

def quotRep : stabAlg M' K →ₐ[ℂ] Module.End ℂ (M' ⧸ K.comap M'.subtype) where
  toFun := restrictQ
  map_one' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_mul' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_zero' := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  map_add' f g := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl
  commutes' r := by
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    rfl

variable (M' K) in

def quotIncl : (M' ⧸ K.comap M'.subtype) →ₗ[ℂ] M ⧸ K :=
  (K.comap M'.subtype).liftQ (K.mkQ ∘ₗ M'.subtype) fun x hx => by simpa using hx

theorem quotIncl_injective : Function.Injective (quotIncl M' K) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ fun x hx => by simpa using hx

theorem quotIncl_quotRep (b : stabAlg M' K) (v : M) (hv : v ∈ M') :
    quotIncl M' K (quotRep M' K b (Submodule.Quotient.mk ⟨v, hv⟩)) = K.mkQ (b.1 v) := rfl

end GlobalTheory.LeviHC.QuotMonic

namespace GlobalTheory.LeviHC.QuotMonic

open Algebra in

theorem monicFactorFiniteMod_of (H : MonicFactorFinite) : MonicFactorFiniteMod := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hM hK hc v hv hfin
  classical
  set S := stabAlg M' K
  have hpB : ∀ u, p u ∈ S := fun u x hx => ⟨(hM u x hx).2.1, fun hk => (hK u x hk).1⟩
  have hqB : ∀ u, q u ∈ S := fun u x hx => ⟨(hM u x hx).2.2, fun hk => (hK u x hk).2⟩
  have hcB : ∀ u, c u ∈ S := fun u x hx => ⟨(hM u x hx).1, fun hk =>
    (K.sub_mem_iff_left (hK u _ (hK u x hk).2).1).1 (hc u x hx)⟩
  let pS : ℂ → S := fun u => ⟨p u, hpB u⟩
  let qS : ℂ → S := fun u => ⟨q u, hqB u⟩
  let cS : ℂ → S := fun u => ⟨c u, hcB u⟩
  let ρ := quotRep M' K

  have poly : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, r u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
      ∃ (d : ℕ) (a : ℕ → Module.End ℂ (M' ⧸ K.comap M'.subtype)), a d = 1 ∧
        ∀ u, ρ ⟨r u, hr u⟩ = ∑ i ∈ Finset.range (d + 1), u ^ i • a i := by
    intro r hr ⟨d, a, ha1, hra⟩
    have haB : ∀ i < d + 1, a i ∈ S := fun i hi =>
      (Subalgebra.mem_toSubmodule S).1 ((Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hr u))
        (coeff_mem_span hra hi))
    let a' : ℕ → S := fun i => if h : a i ∈ S then ⟨a i, h⟩ else 0
    have ha' : ∀ i < d + 1, (a' i).1 = a i := fun i hi => by simp [a', haB i hi]
    refine ⟨d, fun i => ρ (a' i), ?_, fun u => ?_⟩
    · have : a' d = 1 := Subtype.ext ((ha' d (Nat.lt_succ_self d)).trans ha1)
      show ρ (a' d) = 1
      rw [this, map_one]
    · have e : (⟨r u, hr u⟩ : S) = ∑ i ∈ Finset.range (d + 1), u ^ i • a' i := by
        apply Subtype.ext
        change r u = _
        rw [hra u]
        rw [show ((∑ i ∈ Finset.range (d + 1), u ^ i • a' i : S) : Module.End ℂ M) = ∑ i ∈ Finset.range (d + 1), u ^ i • (a' i : Module.End ℂ M) from
          map_sum S.val.toLinearMap (fun i => u ^ i • a' i) _ |>.trans (Finset.sum_congr rfl fun i _ => map_smul S.val.toLinearMap _ _)]
        exact Finset.sum_congr rfl fun i hi => by rw [ha' i (Finset.mem_range.1 hi)]
      rw [e, map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  have hcS : ∀ u, ρ (cS u) = ρ (pS u) * ρ (qS u) := fun u => by
    rw [← map_mul]
    refine LinearMap.ext fun y => Submodule.Quotient.induction_on _ y fun x => ?_
    obtain ⟨x, hx⟩ := x
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq]
    simpa using hc u x hx

  have hval : ∀ (r : ℂ → Module.End ℂ M) (hr : ∀ u, r u ∈ S),
      (adjoin ℂ (Set.range fun u => (⟨r u, hr u⟩ : S))).map S.val = adjoin ℂ (Set.range r) := by
    intro r hr
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  have hrho : ∀ (s : ℂ → S), adjoin ℂ (Set.range fun u => ρ (s u)) = (adjoin ℂ (Set.range s)).map ρ := by
    intro s
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    rfl
  set v' : M' ⧸ K.comap M'.subtype := Submodule.Quotient.mk ⟨v, hv⟩
  have hj := quotIncl_injective (M' := M') (K := K)
  have key := H (M' ⧸ K.comap M'.subtype) (fun u => ρ (pS u)) (fun u => ρ (qS u)) (poly p hpB hp) (poly q hqB hq)
    (fun u u' => (show Commute (pS u) (pS u') from Subtype.ext (hpp u u').eq).map ρ)
    (fun u u' => (show Commute (qS u) (qS u') from Subtype.ext (hqq u u').eq).map ρ)
    (fun u u' => (show Commute (pS u) (qS u') from Subtype.ext (hpq u u').eq).map ρ) v' ?_
  ·
    haveI := key
    unfold FinMod
    refine Submodule.finiteDimensional_of_le (?_ : _ ≤ Submodule.map (quotIncl M' K)
      (Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u)), y = a v'}))
    rw [Submodule.map_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← hval p hpB] at ha
    obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
    refine Submodule.subset_span ⟨ρ b v', ⟨ρ b, ?_, rfl⟩, quotIncl_quotRep b v hv⟩
    rw [hrho pS]
    exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
  · haveI : FiniteDimensional ℂ (Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)}) := hfin
    set T := Submodule.span ℂ {y | ∃ a ∈ adjoin ℂ (Set.range fun u => ρ (pS u) * ρ (qS u)), y = a v'}
    have hle : T.map (quotIncl M' K) ≤
        Submodule.span ℂ {y : M ⧸ K | ∃ a ∈ adjoin ℂ (Set.range c), y = K.mkQ (a v)} := by
      rw [Submodule.map_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have e : (fun u => ρ (pS u) * ρ (qS u)) = fun u => ρ (cS u) := funext fun u => (hcS u).symm
      rw [e, hrho cS] at ha
      obtain ⟨b, hb, rfl⟩ := Subalgebra.mem_map.1 ha
      refine Submodule.subset_span ⟨b.1, ?_, quotIncl_quotRep b v hv⟩
      rw [← hval c hcB]
      exact Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hj T).symm

end GlobalTheory.LeviHC.QuotMonic
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def derEnd {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : Module.End ℂ (SmG σ J) where
  toFun f := ⟨lineDer γ f.1, isSm_lineDer f.2 hγ⟩
  map_add' f f' := Subtype.ext (lineDer_add f.2 f'.2 hγ)
  map_smul' a f := Subtype.ext (lineDer_smul a f.1 γ)

theorem exists_isDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ D, IsDer σ J τ D := by
  classical
  let ρ : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (SmG σ J) := fun Z =>
    if hZ : ∃ γ, IsLineOf σ J τ Z γ then derEnd (hZ.choose_spec.isRealLine h) else 0
  have hρ : ∀ Z γ, IsLineOf σ J τ Z γ → ∀ f : SmG σ J, (ρ Z f).1 = lineDer γ f.1 := fun Z γ hγ f => by
    have hZ : ∃ γ, IsLineOf σ J τ Z γ := ⟨γ, hγ⟩
    simp only [ρ, dif_pos hZ]
    rw [hγ.unique h hZ.choose_spec]; rfl
  obtain ⟨D, h1, h2⟩ := GlobalTheory.T.lie_algebra_rep_derivation_matrix n (J.map τ.1) (conjTranspose_map h hJ τ.1) (isUnit_det_map hJ τ.1) _ ρ
    (fun X X' hX hX' => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      obtain ⟨δ, hδ⟩ := exists_isLineOf h hJ hX'
      obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X + X') h hJ (by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hX', add_zero])
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.add_apply, Submodule.coe_add, hρ _ _ hγ, hρ _ _ hδ, hρ _ _ hε]
      exact (GlobalTheory.T.line_derivative_additive F E σ h n J hJ w τ f.1 f.2 X X' γ δ ε hγ hδ).1 hε)
    (fun c X hX => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, hρ _ _ hγ, hρ _ _ (hγ.smul c)]
      funext g
      have hd := ((differentiable_of_isSm f.2 (hγ.isRealLine h) g) (0 * c)).hasDerivAt.scomp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).mul_const c)
      have := hd.deriv
      simp only [zero_mul, one_mul] at this
      simpa [lineDer, Function.comp_def] using this)
    (fun X X' hX hX' => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      obtain ⟨δ, hδ⟩ := exists_isLineOf h hJ hX'
      obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X * X' - X' * X) h hJ (by
        have e1 := eq_neg_of_add_eq_zero_left hX
        have e2 := eq_neg_of_add_eq_zero_left hX'
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc,
          Matrix.mul_assoc, e1, e2, Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2,
          Matrix.mul_sub]
        simp [Matrix.mul_assoc])
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply, hρ _ _ hγ, hρ _ _ hδ,
        hρ _ _ hδ, hρ _ _ hγ, hρ _ _ hε]
      exact (GlobalTheory.T.line_derivative_additive F E σ h n J hJ w τ f.1 f.2 X X' γ δ ε hγ hδ).2 hε)
  exact ⟨D, h1, fun Z γ hγ f => by rw [h2 Z (hγ.skew h)]; exact hρ Z γ hγ f⟩

theorem glRel_frame {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B)
    (hD : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ}
    (hRQ : R * Q = 1) : GlRel fun a b : Fin m => D (Q * Matrix.single a b (1 : ℂ) * R) := by
  intro a b c d
  have e : ∀ a b c d : Fin m, Q * Matrix.single a b (1 : ℂ) * R * (Q * Matrix.single c d (1 : ℂ) * R) =
      if b = c then Q * Matrix.single a d (1 : ℂ) * R else 0 := fun a b c d => by
    have : Q * Matrix.single a b (1 : ℂ) * R * (Q * Matrix.single c d (1 : ℂ) * R) =
        Q * (Matrix.single a b (1 : ℂ) * (R * Q) * Matrix.single c d 1) * R := by simp only [Matrix.mul_assoc]
    rw [this, hRQ, Matrix.mul_one]
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp
  rw [← hD, e, e, map_sub]
  congr 1 <;> split_ifs <;> simp

theorem eq_sum_frame {m : ℕ} {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ} (hQR : Q * R = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) : X = ∑ a, ∑ b, (R * X * Q) a b • (Q * Matrix.single a b (1 : ℂ) * R) := by
  have e : ∑ a, ∑ b, (R * X * Q) a b • (Q * Matrix.single a b (1 : ℂ) * R) =
      Q * (∑ a, ∑ b, Matrix.single a b ((R * X * Q) a b)) * R := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, ← Matrix.matrix_eq_sum_single]
  simp only [← Matrix.mul_assoc, hQR, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQR, Matrix.mul_one]

theorem qdet_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (u : ℂ) : qdet X u ∈ S := by
  unfold qdet Formalism.REAL.qminor
  refine S.sum_mem fun π _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  exacts [S.algebraMap_mem _, S.zero_mem]

theorem gelfA_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (k : ℕ) : gelfA X k ∈ S := by
  unfold gelfA
  refine S.sum_mem fun π _ => S.list_prod_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  exact hS _ _

theorem finite_of_gelf (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)) (hD : ∀ w, IsDer σ J (τ w) (D w))
    (v : SmG σ J) (hv : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ {x | ∃ a ∈ Algebra.adjoin ℂ
      (Set.range (gelfA fun a b => D w (Matrix.single a b 1))), x = a v})) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z v.1}) := by
  classical
  let X : InfinitePlace F → Fin n → Fin n → Module.End ℂ (SmG σ J) := fun w a b => D w (Matrix.single a b 1)
  have hG : ∀ w, GlRel (X w) := fun w => by
    simpa using glRel_frame (D w) (hD w).1 (Q := 1) (R := 1) (Matrix.mul_one _)
  have hc : ∀ w w', w ≠ w' → ∀ a b c d, X w a b * X w' c d = X w' c d * X w a b := fun w w' hne a b c d =>
    GlobalTheory.T.derivations_commute_distinct_places F E σ h n J hJ w (τ w) (D w) (hD w) w' (τ w') (D w') (hD w') hne _ _
  obtain ⟨W, hW, hvW, hs⟩ := GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable (SmG σ J) (InfinitePlace F)
    (fun w => Algebra.adjoin ℂ (Set.range (gelfA (X w)))) (fun w w' hne a ha b hb => by
      have h1 : ∀ c d, a * X w' c d = X w' c d * a := fun c d => by
        have : Algebra.adjoin ℂ (Set.range (gelfA (X w))) ≤ Subalgebra.centralizer ℂ {X w' c d} := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨k, rfl⟩
          exact gelfA_mem _ _ (fun a b => by rintro _ rfl; exact (hc w w' hne a b c d).symm) k
        exact (this ha _ rfl).symm
      have : Algebra.adjoin ℂ (Set.range (gelfA (X w'))) ≤ Subalgebra.centralizer ℂ {a} := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨k, rfl⟩
        exact gelfA_mem _ _ (fun c d => by rintro _ rfl; exact h1 c d) k
      exact this hb _ rfl) v hv
  let A := Algebra.adjoin ℂ (Set.range fun p : InfinitePlace F × Fin n × Fin n => X p.1 p.2.1 p.2.2)
  have hDA : ∀ w Z, D w Z ∈ A := fun w Z => by
    rw [Matrix.matrix_eq_sum_single Z]
    simp only [map_sum]
    refine A.sum_mem fun a _ => A.sum_mem fun b _ => ?_
    rw [← mul_one (Z a b), ← smul_eq_mul, ← Matrix.smul_single, map_smul]
    exact A.smul_mem (Algebra.subset_adjoin ⟨(w, a, b), rfl⟩) _
  have hword : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ u ∈ A, ∀ f : SmG σ J, l.foldr lineDer f.1 = (u f).1 := fun l => by
    induction l with
    | nil => exact fun _ => ⟨1, A.one_mem, fun f => rfl⟩
    | cons γ l ih =>
      intro hl
      obtain ⟨u, hu, e⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
      obtain ⟨w, Z, hZ⟩ := GlobalTheory.T.real_line_is_line_of_place F E σ h n J hJ τ γ (hl γ List.mem_cons_self)
      exact ⟨D w Z * u, A.mul_mem (hDA w Z) hu, fun f => by
        rw [List.foldr_cons, e, Module.End.mul_apply, (hD w).2 Z γ hZ]⟩
  refine Submodule.finiteDimensional_of_le (S₂ := W.map (SmG σ J).subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  choose! u hu he using fun l (hl : l ∈ z.support) => hword l (hz.1 l hl)
  let U := ∑ l ∈ z.support, z l • u l
  have hU : ∀ f : SmG σ J, dop z f.1 = (U f).1 := fun f => by
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    funext g
    simp only [dop, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← he l hl]
  have hline : ∀ w Z γ, IsLineOf σ J (τ w) Z γ → D w Z * U = U * D w Z := fun w Z γ hγ =>
    LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, Module.End.mul_apply, (hD w).2 Z γ hγ, ← hU, ← hU, (hD w).2 Z γ hγ]
      exact GlobalTheory.UAut.CentralComm.lineDer_dop_comm F E σ n J z hz f.1 f.2 γ (hγ.isRealLine h))
  have hmem := GlobalTheory.T.centre_generated_by_gelfand GlobalTheory.T.relativeCentre' _ _ n X hG hc U (A.sum_mem fun l hl => A.smul_mem (hu l hl) _) fun w a b => by
    obtain ⟨γ₁, γ₂, h1, h2, e⟩ := exists_lines h hJ (τ w) (Matrix.single a b 1)
    change D w _ * U = U * D w _
    rw [e, map_add, map_smul (D w) Complex.I, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hline w _ _ h1,
      hline w _ _ h2]
  have key : ∀ a ∈ Algebra.adjoin ℂ (Set.range fun p : InfinitePlace F × ℕ => gelfA (X p.1) p.2), ∀ x ∈ W, a x ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hs p.1 _ (Algebra.subset_adjoin ⟨p.2, rfl⟩)
    | algebraMap r => intro x hx; exact W.smul_mem r hx
    | add x y _ _ hx hy => intro f hf; exact add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; exact hx _ (hy f hf)
  exact ⟨U v, key U hmem v hvW, (hU v).symm⟩

end General

theorem frame_unit_apply {n m : ℕ} {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ} (hRQ : R * Q = 1)
    (p q : Fin m) : R * (Q * Matrix.single p q (1 : ℂ) * R) * Q = Matrix.single p q 1 := by
  have : R * (Q * Matrix.single p q (1 : ℂ) * R) * Q = R * Q * Matrix.single p q (1 : ℂ) * (R * Q) := by
    simp only [Matrix.mul_assoc]
  rw [this, hRQ, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.LeviHC

end
end
