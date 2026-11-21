import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTerTer
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfLabelsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurtherStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTameAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmDZOfLabels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockVectorNotKilledStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlockVectorNotKilled
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreLastStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionIsoSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionIsoSplitPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTameLabelMu

section
section
set_option synthInstance.maxHeartbeats 200000

section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf →
    DepthZ D := by
  intro hP hS hL D P hrow hlab hchi
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hrow
  have hfix : ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
      TameLP D (D.naut.locV i PI (D.naut.plGw k v)) := by
    intro i PI k v
    have hw := GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
    have htame := _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw hL D P S hT i k v hw
    have hTB := _root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hT i _ hw ⟨k, D.naut.plGw_over k v⟩ htame
    obtain ⟨x, hx0, hx⟩ := hTB.2 PI
    have hfixd : x ∈ GlobalTheory.PRep.fixed ((S i _ hw).rep PI).π
        (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
      intro h
      have h' : ((S i _ hw).rep PI).π h x = x := GlobalTheory.JacBlock.KOne_le_stab htame hx h.2
      simpa using h'
    have hwild := _root_.GlobalTheory.DepthZeroLoc.main_m_alt hP.bz hS hL D _ _ ((S i _ hw).rep PI) ⟨x, hfixd, hx0⟩
      (UpperTheory.One.M.isQg_of_over D k _ (D.naut.plGw_over k v))
    intro σ hσI hσW
    have hd : D.naut.lpDim (D.naut.locV i PI (D.naut.plGw k v)) = D.R.r + D.R.t := by
      rw [← P.T.dim, (S i _ hw).locV PI, (hLaws i _ hw).dim]
    rw [P.T.inePol _ _ σ hσI, (S i _ hw).locV PI, hT.rc i _ hw, hwild σ hσW, hd]
  intro i PI k w hw
  obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact hfix i PI k v
  · exact ((_root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hlab) i PI k v w hc).2.1 (hfix i PI k v)
end GlobalTheory.DepthZeroTame
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → DepthZ D := by
  atlas_forward_decl _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.BlockTypeSplit
open ValuativeRel Polynomial
section Finite
end Finite
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {p : ℕ} [Fact p.Prime] {r t : ℕ}
theorem block_type_split_local_alt (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hp : resCard F = p) (L : GlobalTheory.GLq.LabelDatum p) {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχt : IsTame χ) {θ : (ZMod p)ˣ →* ℂˣ} (hθχ : CharLift θ χ) {u : ZMod p}
    (hθ : GlobalTheory.GLp.IsCharLab L θ u) (π : Irr F (r + t)) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hu : ¬ f.IsRoot u) {x : π.V}
    (hx : IsBlockVec χ π.π x) (hxρ : NotKilled π.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) x) :
    ∃ (π₁ : Irr F r) (π₂ : Irr F t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y := by
  classical
  have hBZ := hP.bz
  have hG := hP.geo
  have hM := hP.mp
  obtain ⟨v, hv, hb, ℓ, hℓ, hzv⟩ := GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent F p r t χ _ π.π _ x hp (GlobalTheory.SerOSys.zIdem_idem_central ρ hρ).1 hx hxρ
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy, hyρ⟩ :=
    GlobalTheory.T.tame_character_parahoric_invariant hM F p r t χ _ π.π _ v ℓ hp π.smooth π.irr hχt hv hb hℓ hzv
  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hG hP.unl hM F r t χ π v hχ hχt hv hb
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨-, hσ, e₀, hπσ⟩ := hsupp
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2 e₀
      (two (stdSum (rfl : r + t = r + t))) (fun a => (σ a).smooth)
      (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _) hπσ))
    set A := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar F α)))} with hA
    obtain ⟨i, hi, hi0⟩ : ∃ i ∈ A, b.1 i true = 0 := by
      by_contra! hc
      have h2 := b.2.2 true
      have h3 : A.ncard ≤ ∑ i, b.1 i true := by
        rw [Set.ncard_eq_toFinset_card' A, Finset.card_eq_sum_ones]
        exact (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hc i (Set.mem_toFinset.1 hi))).trans
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨hd, α, hα⟩ := hi
    have hi1 : b.1 i false = 1 := by
      have h1 := b.2.1 i
      simp [Fintype.sum_bool] at h1
      omega
    have hact := GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral F _ Bool (b.1 i) (fr i) _ (σ i).π _ (S i) hα (hrow i) false
    obtain ⟨w, hw⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ, hφ0, hφ⟩ := GlobalTheory.T.exists_equivariantMap_of_levelTypeVector F p (Fin r) _ _ ρ w hp hw
    obtain ⟨v', hv', hpar⟩ := GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap F p (Fin s) (Fin r) (fun i => Fin (b.1 i false)) (gc false) _
      (fun i => (S i false).ρ) i θ χ _ ρ.ρ φ hp hθχ (fun g hg v => by
        rw [hact g hg v, MonoidHom.mul_apply,
          isUnram_unrChar F α _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg), mul_one]) hφ0 hφ
    exact hu (isRoot_of_parVec L (gc false) i ρ hρ hf hθ (by rw [Fintype.card_fin, hi1]) hv' hpar)
  · obtain ⟨π₁, π₂, ⟨φ⟩, hno⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hG hP.unl F r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hG hM F r t χ π π₁ π₂ v hχ hχt hno ⟨φ⟩ hv hb
    refine ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχ.inv, hsph, ?_, ?_⟩
    · have h := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
      rw [inv_inv] at h
      show Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
      rw [h]
      exact ⟨φ⟩
    obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd F r t _ _ π₁.π π₂.π
    let Ψ := φ.trans E
    have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact π₁.smooth
      · exact π₂.smooth
    have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact hasFiniteLength_of_isIrreducible π₁.irr
      · exact hasFiniteLength_of_isIrreducible π₂.irr
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2
      (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _)
        (IsSubquotient.of_injective Ψ.toIntertwiningMap Ψ.toLinearEquiv.injective)))
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (gc j) fun i => (S i j).ρ)
      Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0 hy
    obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity F Bool (fun i => Fin (b.1 i true)) (Fin t) (gc true) _
      (fun i => (S i true).ρ) χ z hz0 hz
    have hm : b.1 false true = 0 := by
      by_contra hm
      obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (fun i => Fin (b.1 i true)) _ (fun i => (S i true).ρ) _
        (piTensor fun i => (S i true).ρ) false χ w (fun i => (S i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
      obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hM F _ _ (S false true).ρ χ z' (S false true).smooth (S false true).irr hχ
        (Nat.pos_of_ne_zero hm) hz'0 hz'
      exact hno α (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG F r _ π₁.π Bool (b.1 false) (fr false) (S false) true _ π₁.smooth (hrow false) hα)
    have hm' : b.1 true false = 0 := by
      have h1 := b.2.1 false
      have h2 := b.2.2 false
      simp [Fintype.sum_bool] at h1 h2
      omega
    obtain ⟨w₁, hw₁⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ₁, h1⟩ := GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock F r (b.1 false) (fr false) _ π₁.π (S false) hm (hrow false)
    obtain ⟨φ₂, h2⟩ := GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first F r (fun i => b.1 i false) (gc false) (fun i => S i false) hm'
    obtain ⟨y₁, hy₁⟩ := TypeVec.up π₁.smooth (h2.trans ((GlobalTheory.T.isSubquotientRepresentation_two_reindexings F _ _ φ₂ φ₁ _ (S false false).ρ).trans h1)) hw₁
    exact ⟨y₁, typeVec_iff _ _ _ hy₁⟩
end Local
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D),
    GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  intro hP hL D Γ hΓ k v χ hχ u π ρ f ht hlab hser hu ⟨x, hx, hxρ⟩
  have hchi := _root_.UpperTheory.Lit.Dz.localGlobalCompatibility_cmDatum_alt hL D Γ k v χ hχ u ht hlab
  have h0 : idemOf D k ρ ≠ 0 := fun e => by
    obtain ⟨ℓ, -, h⟩ := hxρ
    refine h ?_
    rw [e]
    simp
  obtain ⟨L, h1, h2, hf⟩ := @exists_hasLabel _ ⟨D.host.g_prime k⟩ _ (D.ntypes.teichC_inj k) _ (Γ.ζ_gen k) (Γ.O k) (hΓ k)
    _ ρ hser.1 f h0 (by rw [← Γ.eSer_def]; exact hser.2)
  refine (And.right hchi L h1 h2).elim fun θ hθ => ?_
  exact @_root_.GlobalTheory.BlockTypeSplit.block_type_split_local_alt _ _ _ _ _ _ ⟨D.host.g_prime k⟩ _ _ hP (And.left hchi) L χ hχ ht θ hθ.1 u hθ.2 π ρ hser.1 f hf hu x hx hxρ
end GlobalTheory.BlockTypeSplit
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  first | exact @_root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeVecEig
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  intro hL D P S hT i PI k v s hw hsw c hcont hci F _hF x hx hh
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    rw [show c _ = c.toRingHom _ from rfl, RingHom.map_det]
    congr 1
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ := hT.mu i s.w hw j hj
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci (S i s.w hw).mu ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar (S i s.w hw).mu h =
      (((S i s.w hw).mu (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar (S i s.w hw).mu h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]
end GlobalTheory.TypeVecEig
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_iso_split_place_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  atlas_forward_decl _root_.GlobalTheory.TypeVecEig.main_alt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem vector_at_split_place (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hC : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (S : Reading P.T)
    (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (hw : IsSplitPl D.host s.w) (hs : s.w = D.naut.plGw k v) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (hρ : CategoryTheory.Simple ρ) (hocc : PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ)) :
    ∃ x, IsBlockVec (S i s.w hw).mu ((S i s.w hw).rep PI).π x ∧ NotKilled ((S i s.w hw).rep PI).π (idemOf D k ρ) x := by
  classical
  obtain ⟨c, T, hc, hcs, -, -, -⟩ := hT.rep i s hw PI
  obtain ⟨F, hF, hne⟩ := hocc
  set z := idemOf D k ρ with hz
  have hzc : ∀ b, z * b = b * z := by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  have hcen := GlobalTheory.SeriesSupportTest.atPlace_central D k v z hzc
  obtain ⟨L, hLift, hCL⟩ := hC i
  have e : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dif_pos hcen]; exact hCL ⟨_, hcen⟩ F
  have hne' : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) ≠ 0 := by
    rw [← e]; intro h0; apply hne; exact (P.M.loc i).real_inj (h0.trans (map_zero _).symm)
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) =
      ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i PI k v s hs c hc hcs L hLift F hF h (g h) (by simp [g]) (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hne'' : ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) ≠ 0 := by
    rw [hsum] at hne'
    simpa only [(hxs _).2.2] using hne'
  obtain ⟨U, hU, h1U, hθU⟩ := GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one _ D.R.r D.R.t (S i s.w hw).mu (S i s.w hw).mu_ok.1
  have hFS : (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i PI) := by
    have := hF; rw [P.H.av.typeV] at this; exact this
  obtain ⟨y, hy, hyz⟩ := GlobalTheory.T.local_component_continuous_iso_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i PI) (P.H.av.irr i PI) s
    ((S i s.w hw).rep PI).toIrrRep (hT.rep i s hw PI) c hc hcs (GlobalTheory.BlockType.blockGrp _ D.R.r D.R.t)
    (GlobalTheory.BlockType.blockChar (S i s.w hw).mu) U (fun h hh => hh.1) (GlobalTheory.BlockType.kOne_le_blockGrp _ _) hU h1U
    (fun g hg _ => hθU g hg) _ hFS (_root_.GlobalTheory.T.completion_iso_split_place_alt hL D P S hT i PI k v s hw hs c hc hcs F hF) _ xs (fun h => z.coeff h)
    (fun h => (hxs h).1) hne''
  refine ⟨y, GlobalTheory.BlockType.isBlockVec_of _ _ _ hy, fun h => Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV (xs h)), fun h => (hxs h).2.1, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact hyz
end GlobalTheory.DzVecLoc
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  intro _ hL D P hC S hT i PI k v hw ρ f hser hocc
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hw
  have key : ∀ (w : PlE D.host) (hw' : IsSplitPl D.host w), w = D.naut.plGw k v → ∃ x, IsBlockVec (S i w hw').mu ((S i w hw').rep PI).π x ∧ NotKilled ((S i w hw').rep PI).π (idemOf D k ρ) x := by
    intro w hw' hwv
    have e : w = s.w := hwv.trans hs.symm
    subst e
    exact _root_.GlobalTheory.DzVecLoc.vector_at_split_place hL D P hC S hT i PI k v s hw' hs ρ hser.1 hocc
  exact key _ hw rfl
end GlobalTheory.DzVecLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  first | exact @_root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRow
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  intro hP hL D P hRow hLab hCen hGreen hChi
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hRow
  have hLoc : _root_.GlobalTheory.PendOf.LocalDatumCondition hL D := _root_.GlobalTheory.DepthZeroAssembly.locDZ_of_split_reg_m_alt hL D
    (_root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero hP hL D P.ty.grp hGreen) (_root_.UpperTheory.Lit.Dz.blockTypeSplitProp hP hL D P.ty.grp hGreen)
  have hConj : ConjDual D := _root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hLab
  intro i k v PI
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro ρ f hρ hser hocc hsq hu
  have hw : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs hP hL D P hCen S hS i PI k v hw ρ f ⟨hρ, hser⟩ hocc
  obtain ⟨htame, hχ, u, hu', hlabχ⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hP hL D P hChi S hS i k v hw
  obtain ⟨hmono, hlab⟩ := hLoc k v (S i _ hw).mu hχ (u : ZMod (D.host.g k)) ((S i _ hw).rep PI) ρ f htame hlabχ
    ⟨hρ, hser⟩ hsq (hu u hu') ⟨x, hx⟩
  have hrc : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) _ ((S i _ hw).rep PI) = P.T.e _ (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [← hS.rc i _ hw]
    exact ((S i _ hw).locV PI).symm
  have hm0 : D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [hrc] at hmono
    exact (P.T.mono0 _ _).2 hmono
  have hl : D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t := by
    rw [P.lab k v, ← hlab]
    unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
    rw [hrc]
  have hf0 : D.ntypes.eSer k f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hser
    exact GlobalTheory.SerOSys.ZSum.zIdem_ne_zero ρ hρ hser.symm
  have hdegf : f.natDegree = D.R.r := by
    by_contra hne
    exact hf0 (D.ntypes.eSer_zero k f fun h => hne h.2.1)
  have hfne : f ≠ 0 := by
    intro h; apply hf0; exact D.ntypes.eSer_zero k f fun h' => by rw [h] at h'; exact (h'.1.ne_zero rfl)
  have hdeg : (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t).natDegree = D.R.nV := by
    rw [natDegree_mul hfne (pow_ne_zero _ (X_sub_C_ne_zero _)), natDegree_pow, natDegree_X_sub_C, hdegf, mul_one]
    rfl
  refine ⟨u, hu', hm0, hl, fun w' hc => ?_⟩
  obtain ⟨hc1, -, hc3⟩ := hConj i PI k v w' hc
  have hroots : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹) := by
    rw [hc3, hl]
  refine ⟨hc1 hm0, ?_, hroots⟩
  rw [← card_rootsBar, hroots, Multiset.card_map, card_rootsBar, hdeg]
end GlobalTheory.DepthZeroRow
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  first | exact @_root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PinClose
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → SumRepresentations.tie0 D → SumRepresentations.adm5 D →
    ZLStable D → CenInt D → SerLL D → CoeffRingsHaveRootsOfUnity D → ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hPr hSu hL D P hRow hLab hCen hGr hChi ht0 ha5 hZL hCI hSer hZ
  obtain ⟨hIne, hDep, hGen⟩ := GlobalTheory.LabTies.main D P.T hLab
  have hCT : OnMtPreservesTypeV D := GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations D P.M P.H.av hCen
  have hDZ : DepthZ D := _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk hPr hSu hL D P hRow hLab hChi
  have hAdm : PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab hPr hL D P hRow hLab hCen hGr hChi
  have hPar : ∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par,
      ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w := by
    intro S
    refine ⟨P.ty.par.eP.symm ⟨S.1, S.2⟩, fun w => ?_⟩
    rw [P.ty.par.locPar_def]
    have e := P.ty.par.eP.apply_symm_apply (⟨S.1, S.2⟩ : HeightCounting.ParC D)
    rw [e]
  exact GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan D P.M P.H.hecke P.H.rational P.H.av hPar ht0 ha5 hIne hDep hGen hZL hCI hCT hSer hZ hDZ hAdm
end GlobalTheory.PinClose
end
end
end
