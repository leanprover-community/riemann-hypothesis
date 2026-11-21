import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaFunOrientedModelCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroThetaFunOrientedModelCm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.StandardAdditiveCharacterSign
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIsomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlaceStatement
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SplitPlaceThetaFunctionVacuumConjugatePlace
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilOrthogonalFiniteCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsFinsetAnnLeK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsThetaFunOFHeisOFK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeisOFDblGDeltaTK

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.ThetaNonzeroF
theorem exists_isThetaFunOF_ne_zero_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ
  have hstd := _root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let JA : Matrix (Fin nT) (Fin nT) E := JTᵀ
  let JB : Matrix (Fin nS) (Fin nS) E := -(ξ₀ • JS⁻¹)
  have hSinv := herm_inv_entry σ JS hS.1 (Ne.isUnit hS.2)
  have hA : ∀ i j, σ (JA j i) = JA i j := fun i j => hT.1 j i
  have hBs : ∀ i j, σ (JB j i) = -JB i j := fun i j => by
    simp only [JB, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, map_neg, map_mul, hσξ, hSinv]
    ring
  have hA' : JA.det ≠ 0 := by simp only [JA, Matrix.det_transpose]; exact hT.2
  have hB' : JB.det ≠ 0 := by
    simp only [JB, Matrix.det_neg, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : E) ≠ 0))
      (mul_ne_zero (pow_ne_zero _ hξ0) (Matrix.isUnit_nonsing_inv_det JS (Ne.isUnit hS.2)).ne_zero)
  obtain ⟨co, hco⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hA hBs hA' hB'
  let co' : Darboux (symp (cA σ) (-1 : AF F ⊗[F] E) (incM F JA) (incM F JB)) (Fin nT × Fin nS) := co
  have hrat : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin nT × Fin nS → F,
      co'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := hco
  have hJA : JA = JTᵀ := rfl
  have hJB : (-1 : AF F ⊗[F] E) • incM F JB = incM F (ξ₀ • JS⁻¹) := by
    ext i j
    simp [JB, incM]
  let τ := Fintype.equivFin (Fin nT × Fin nS)
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co' τ w) (GlobalTheory.TransportF.numCoordF co' τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hJA hJB, co'.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card (Fin nT × Fin nS)) → F,
      GlobalTheory.TransportF.numCoordF co' τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  obtain ⟨Φ, hΦ, hne⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin nT × Fin nS)
  refine ⟨GlobalTheory.WeilSchrodinger.thetaTr F co' B.ψ Φ, ?_, ?_⟩
  · rw [GlobalTheory.TransportF.thetaTr_eqF co' τ]
    exact _root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hstd _ (GlobalTheory.TransportF.numCoordF co' τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  · intro h
    have h0 := congrFun h 0
    apply hne
    have hs : GlobalTheory.WeilM.schr B.ψ (0 : (Fin nT × Fin nS → AF F) × (Fin nT × Fin nS → AF F)) Φ = Φ := by
      funext x
      simp [GlobalTheory.WeilM.schr]
    simpa [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hs] using h0
end GlobalTheory.ThetaNonzeroF
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_nonzero_theta_function : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∃ f₀ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 := by
  atlas_forward_decl _root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero_k
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
theorem PositivityTheory.ThKW.exists_finite_open_subgroup_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) →
        ∃ G : Finset (WOF F E nS nT), (∀ g ∈ G, ∀ i j, e * g i j = g i j) ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            (∀ g ∈ G, B.ψ (symplOHF σ JS JT ξ₀ g y - symplOHF σ JS JT ξ₀ y g) = 1) → y ∈ U :=
  _root_.GlobalTheory.SplitLagrF.exists_finset_ann_le_k
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
open GlobalTheory.SplitInvFormF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
noncomputable section
namespace PositivityTheory.ThKW.SplitVacuumEigenvectors
open GlobalTheory.SplitInvFormF
theorem exists_vac_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  classical
  have he' := isSplitIdemF_conj he
  let Y := conjHalf σ e nS nT
  let X := conjHalf σ (cAF σ e) nS nT
  obtain ⟨U, hU, hUf⟩ := hf₀.level
  obtain ⟨G, hGX, hGU⟩ := _root_.PositivityTheory.ThKW.exists_finite_open_subgroup_split F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he U hU
  have hGX' : ∀ g ∈ G, g ∈ X := fun g hg => mem_conjHalf_conj he (hGX g hg)
  let YK : AddSubgroup (WOF F E nS nT) :=
    { carrier := {y | y ∈ Y ∧ ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1}
      add_mem' := fun {a b} ha hb => ⟨Y.add_mem ha.1 hb.1, fun k hk hkf => by
        rw [commF_add_right, ha.2 k hk hkf, hb.2 k hk hkf, one_mul]⟩
      zero_mem' := ⟨Y.zero_mem, fun k _ _ => commF_zero_right k⟩
      neg_mem' := fun {a} ha => ⟨Y.neg_mem ha.1, fun k hk hkf => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) k a
        rwa [ha.2 k hk hkf, mul_one] at this⟩ }
  let Q : AddSubgroup YK :=
    { carrier := {y | ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1}
      add_mem' := fun {a b} ha hb g hg => by
        rw [AddSubgroup.coe_add, commF_add_right, ha g hg, hb g hg, one_mul]
      zero_mem' := fun g _ => commF_zero_right g
      neg_mem' := fun {a} ha g hg => by
        have := commF_neg_right (σ := σ) (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) g (a : WOF F E nS nT)
        rwa [ha g hg, mul_one] at this }
  have hQfix : ∀ q ∈ Q, heisOF σ JS JT ξ₀ B.ψ (q : WOF F E nS nT) f₀ = f₀ := fun q hq =>
    hUf _ (hGU _ q.2.1 hq) (fin_of_mem he q.2.1)
  have hN : ∀ g ∈ G, ∃ k : ℕ, 0 < k ∧ heisOF σ JS JT ξ₀ B.ψ (k • g) f₀ = f₀ := fun g hg => exists_nsmul_fix he' (hGX' g hg) hf₀
  choose! Ng hNg0 hNg using hN
  set N := ∏ g ∈ G, Ng g with hNdef
  have hN0 : 0 < N := Finset.prod_pos fun g hg => hNg0 g hg
  have hpowN : ∀ g ∈ G, ∀ y : YK, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) ^ N = 1 := by
    intro g hg y
    obtain ⟨m, hm⟩ : Ng g ∣ N := Finset.dvd_prod_of_mem _ hg
    rw [← commF_nsmul_left]
    refine y.2.2 _ (nsmul_mem (hGX' g hg) N) ?_
    rw [hm, mul_nsmul]
    exact heisOF_nsmul_fix he' (nsmul_mem (hGX' g hg) _) (hNg g hg) m
  haveI : Finite (YK ⧸ Q) := by
    let S := (Polynomial.nthRoots N (1 : ℂ)).toFinset
    refine Finite.of_injective (β := G → S) (fun a g => ⟨commF σ JS JT ξ₀ B.ψ g (Quotient.out a : YK), ?_⟩) ?_
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hN0]
      exact hpowN g g.2 _
    · intro a b hab
      rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq]
      intro g hg
      have h1 := congrArg Subtype.val (congrFun hab ⟨g, hg⟩)
      simp only at h1
      show commF σ JS JT ξ₀ B.ψ g ((-Quotient.out a + Quotient.out b : YK) : WOF F E nS nT) = 1
      rw [AddSubgroup.coe_add, commF_add_right, ← h1, AddSubgroup.coe_neg, commF_neg_right]
  let Ch : Set (YK → ℂ) := {χ | ∃ x ∈ X, (∀ q ∈ Q, commF σ JS JT ξ₀ B.ψ x (q : WOF F E nS nT) = 1) ∧ χ = fun y : YK => commF σ JS JT ξ₀ B.ψ x (y : WOF F E nS nT)}
  obtain ⟨χ, ⟨x, hxX, -, rfl⟩, w, hwspan, hw0, hweig⟩ := exists_eigen_of_sep
    (fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT))
    (fun a b f => heisOF_add_half he a.2.1 b.2.1 f) Q f₀ hf₀0 hQfix Ch
    (by rintro _ ⟨x, -, -, rfl⟩ a b; exact commF_add_right x a b)
    (by rintro _ ⟨x, -, hx, rfl⟩ q hq; exact hx q hq)
    (by
      rintro _ ⟨x, hx, hxQ, rfl⟩ _ ⟨x', hx', hxQ', rfl⟩
      refine ⟨x + x', X.add_mem hx hx', fun q hq => by rw [commF_add_left, hxQ q hq, hxQ' q hq, one_mul], ?_⟩
      funext y
      simp only [Pi.mul_apply, commF_add_left])
    ⟨0, X.zero_mem, fun q _ => commF_zero_left _, by funext y; simp only [Pi.one_apply, commF_zero_left]⟩
    (fun y hy => by
      have hy' : ¬ ∀ g ∈ G, commF σ JS JT ξ₀ B.ψ g (y : WOF F E nS nT) = 1 := hy
      push_neg at hy'
      obtain ⟨g, hg, hne⟩ := hy'
      exact ⟨_, ⟨g, hGX' g hg, fun q hq => hq g hg, rfl⟩, hne⟩)
  have hspan_theta : Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ := Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    exact _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hf₀)
  have hspan_fix : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → Submodule.span ℂ (Set.range fun y : YK => heisL σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) ≤
      LinearMap.eqLocus (heisL σ JS JT ξ₀ B.ψ k) LinearMap.id := fun k hk hkf => Submodule.span_le.2 (by
    rintro _ ⟨y, rfl⟩
    show heisOF σ JS JT ξ₀ B.ψ k (heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀) = heisOF σ JS JT ξ₀ B.ψ (y : WOF F E nS nT) f₀
    rw [heisOF_comm, y.2.2 k hk hkf, one_smul, hkf])
  have hwθ : IsThetaFunOF σ JS JT ξ₀ B.ψ w := hspan_theta hwspan
  refine ⟨heisOF σ JS JT ξ₀ B.ψ (-x) w, _root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB nS nT JS JT ξ₀ _ _ hwθ, ?_, ?_⟩
  · intro h0
    apply hw0
    have := heisOF_add_half (JS := JS) (JT := JT) (xi0 := ξ₀) (ψ := B.ψ) he' hxX (X.neg_mem hxX) w
    rw [add_neg_cancel, heisOF_zero] at this
    rw [this, show heisOF σ JS JT ξ₀ B.ψ (-x) w = 0 from h0]
    exact map_zero (heisL σ JS JT ξ₀ B.ψ x)
  · intro y hy
    by_cases hyK : ∀ k ∈ X, heisOF σ JS JT ξ₀ B.ψ k f₀ = f₀ → commF σ JS JT ξ₀ B.ψ k y = 1
    · left
      have hyy : y ∈ YK := ⟨hy, hyK⟩
      have h1 := hweig ⟨y, hyy⟩
      change commF σ JS JT ξ₀ B.ψ x y • heisOF σ JS JT ξ₀ B.ψ y w = w at h1
      rw [heisOF_comm, commF_swap]
      conv_rhs => rw [← h1]
      exact (GlobalTheory.WeilPartsF.heisOF_smul _ _ _).symm
    · right
      push_neg at hyK
      obtain ⟨k, hk, hkf, hne⟩ := hyK
      refine ⟨k, ?_, hne⟩
      rw [heisOF_comm, commF_half he' hk (X.neg_mem hxX), one_smul]
      congr 1
      exact hspan_fix k hk hkf hwspan
end PositivityTheory.ThKW.SplitVacuumEigenvectors
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
theorem _root_.GlobalTheory.T.exists_eigenvector_split_idempotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ φ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ φ ∧ φ ≠ 0 ∧
          ∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
            heisOF σ JS JT ξ₀ B.ψ y φ = φ ∨
            ∃ u : WOF F E nS nT, heisOF σ JS JT ξ₀ B.ψ u φ = φ ∧
              B.ψ (symplOHF σ JS JT ξ₀ u y - symplOHF σ JS JT ξ₀ y u) ≠ 1 := by
  exact @_root_.PositivityTheory.ThKW.SplitVacuumEigenvectors.exists_vac_split_k
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
noncomputable section
namespace GlobalTheory.SplitInvFormF
theorem exists_invForm_split_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨φ, hφ, hφ0, hd⟩ := _root_.GlobalTheory.T.exists_eigenvector_split_idempotent F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.HalfCoinv.exists_form (Y := conjHalf σ e nS nT) (ρ := heisL σ JS JT ξ₀ B.ψ)
    (B := commF σ JS JT ξ₀ B.ψ) (Θ := {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g})
    (fun x hx x' hx' f => by
      show heisOF σ JS JT ξ₀ B.ψ x (heisOF σ JS JT ξ₀ B.ψ x' f) = heisOF σ JS JT ξ₀ B.ψ (x + x') f
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun f => heisOF_zero f) (fun u y f => heisOF_comm u y f)
    (fun u hu g hg => exists_nsmul_fix he hu hg) hφ0 hd
  exact ⟨ℓ, fun u hu f hf => h1 u hu f hf, φ, hφ, h2⟩
end GlobalTheory.SplitInvFormF
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory
theorem _root_.GlobalTheory.T.exists_theta_functional_split_idempotent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  atlas_forward_decl _root_.GlobalTheory.SplitInvFormF.exists_invForm_split_k
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblSplitForm
section Abstract
variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}
end Abstract
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
end GlobalTheory.DblSplitForm
namespace GlobalTheory.DblSplitForm
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF
theorem exists_invForm_dbl_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
  obtain ⟨f₀, hf₀, hf₀0⟩ : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 :=
    _root_.GlobalTheory.T.exists_nonzero_theta_function F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ₁, hℓ₁, f, hf, hℓf⟩ := _root_.GlobalTheory.T.exists_theta_functional_split_idempotent F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  have hheis := _root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := GlobalTheory.SplitInvFormF.conjHalf σ e nS (nT + nT))
    (ρ := GlobalTheory.SplitInvFormF.heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [GlobalTheory.SplitInvFormF.heisOF_heisOF, GlobalTheory.SplitInvFormF.symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => GlobalTheory.SplitInvFormF.heisOF_zero g)
    (fun u hu g hg => GlobalTheory.SplitInvFormF.exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have hu' : ∀ i j, cAF σ e * u i j = u i j := hu
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu' _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j)
        rw [mul_neg, hu']
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁ _ ht a ha, hℓ₁ _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, f, f, hf, hf, ?_⟩
  rw [h2 _ ⟨f, f, hf, hf, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)
end GlobalTheory.DblSplitForm
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.exists_split_functional_doubled : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  atlas_forward_decl _root_.GlobalTheory.DblSplitForm.exists_invForm_dbl_k
end
end
