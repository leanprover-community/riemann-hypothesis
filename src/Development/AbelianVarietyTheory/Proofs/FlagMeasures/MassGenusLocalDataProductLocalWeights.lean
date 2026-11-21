import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassGenusRestrictedProduct
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrincipleStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLatticeClassesFiniteLocalOrbits
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMassStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerDataStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplementStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTermsStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinitePlacesNotPrimeToBaseFrameInvariants

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PhiEmbed

theorem baseChange_injective₂ {D : D7} (p : PlF D) : Function.Injective (baseChange₂ D p) := by
  intro x y hxy
  refine (VS D).frame.ext_elem fun i => ?_
  have := congrFun hxy i
  simp only [baseChange₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  exact (D.s.atP p).ιE.injective this

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩⟩

set_option maxHeartbeats 1000000 in

theorem phi_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∃ φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0), Function.Injective φ ∧ ∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨hext, hUW, -, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  choose e he using fun (g : GV D) (p : PlF D) => (hext g p).exists
  have ext_one : ∀ p, Ext p (1 : GV D) (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := fun p x => rfl
  have ext_mul : ∀ p (a b : GV D) ga gb, Ext p a ga → Ext p b gb → Ext p (a * b) (ga * gb) := by
    intro p a b ga gb ha hb x
    show ga (gb (baseChange₂ D p x)) = baseChange₂ D p (a (b x))
    rw [hb, ha]
  let φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0) :=
    { toFun := fun h p => ⟨e h p, hUW h h.2 p _ (he h p)⟩
      map_one' := by
        funext p
        apply Subtype.ext
        exact (hext 1 p).unique (he _ p) (ext_one p)
      map_mul' := by
        intro a b
        funext p
        apply Subtype.ext
        exact (hext _ p).unique (he _ p) (ext_mul p _ _ _ _ (he a p) (he b p)) }
  refine ⟨φ, ?_, fun h p => he h p⟩
  intro a b hab
  obtain ⟨p⟩ := exists_place D
  have h1 : e a p = e b p := congrArg Subtype.val (congrFun hab p)
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply baseChange_injective₂ p
  rw [← he a p x, ← he b p x, h1]

end GlobalTheory.PhiEmbed
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∃ φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0), Function.Injective φ ∧ ∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := by
  atlas_forward_decl GlobalTheory.PhiEmbed.phi_embed
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GlueOver

theorem exists_locOver : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  intro D Z FP d0 hT hΛ
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hΛ
  have hc : ∀ p, ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ ∧
      ((∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀) →
        τ.abelian₂ = lattice₂ D Z.M p Λ₀) := by
    intro p
    by_cases h : ∃ τ' : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (d0 p) τ' ∧ τ'.abelian₂ = lattice₂ D Z.M p Λ₀
    · obtain ⟨τ', h1, h2⟩ := h
      exact ⟨τ', h1, fun _ => h2⟩
    · obtain ⟨τ', h1⟩ := hT p
      exact ⟨τ', h1, fun h' => absurd h' h⟩
  choose τ hτ hτ' using hc
  obtain ⟨Λ, hΛ, heq⟩ := (GlobalTheory.Unfold.LatLoc.lattices_local_global D Z).2 Λ₀ hΛ₀ (fun p => (τ p).abelian₂)
    (fun p => GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (d0 p) (τ p) (hτ p))
    (hfin.subset (fun p hp h => hp (hτ' p h)))
  exact ⟨Λ, hΛ, fun p => ⟨τ p, hτ p, (heq p).symm⟩⟩

end GlobalTheory.Unfold.GlueOver
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalLattice_over_localInnerData : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (d0 : Dat Z FP), (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ Λ : LV D, LocOver Λ d0 := by
  atlas_forward_decl GlobalTheory.Unfold.GlueOver.exists_locOver
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

theorem gmap_isLattice_rat {D : D7} (g : GV D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g Λ) where
  fg := hΛ.fg.map _
  span_eq_top := by
    have h1 : ((Formalism.HermitianLatticesTheory.gmap g Λ : LV D) : Set (VS D).V) = (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λ : Set (VS D).V) := by
      unfold Formalism.HermitianLatticesTheory.gmap
      rfl
    rw [h1, Submodule.span_image, hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective

theorem ext_fix_lattice_ae : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ h : ↥(FlagPairStabilizer F F'), {p | ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ h
  obtain ⟨-, -, hlat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λ₀) Λ₀ (gmap_isLattice_rat _ _ hΛ₀) hΛ₀).1
  refine hfin.subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  intro heq
  apply hp
  apply Subgroup.subset_closure
  show LocNG.img _ _ = _
  rw [← hlat (h : GV D) p _ Λ₀ (hφ h p)]
  exact heq

end GlobalTheory.Unfold
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ h : ↥(FlagPairStabilizer F F'), {p | ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  atlas_forward_decl GlobalTheory.Unfold.ext_fix_lattice_ae
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DblCos

variable {D : D7}

theorem img_mul (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (a b : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    LocNG.img (a * b) Λ = LocNG.img a (LocNG.img b Λ) := by
  ext x
  simp only [LocNG.img, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    LinearEquiv.mul_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem img_one (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (Λ : Submodule (M p).L.O (Vp D p)) : LocNG.img (1 : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) Λ = Λ := by
  ext x
  simp [LocNG.img]

theorem mem_Aut_iff (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p)) :
    g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg

    let K : Subgroup (Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
      { carrier := {a | LocNG.img a Λ = Λ}
        mul_mem' := fun {a b} ha hb => by
          have ha' : LocNG.img a Λ = Λ := ha
          have hb' : LocNG.img b Λ = Λ := hb
          show LocNG.img (a * b) Λ = Λ
          rw [img_mul p M, hb', ha']
        one_mem' := img_one p M Λ
        inv_mem' := fun {a} ha => by
          have ha' : LocNG.img a Λ = Λ := ha
          show LocNG.img a⁻¹ Λ = Λ
          calc LocNG.img a⁻¹ Λ = LocNG.img a⁻¹ (LocNG.img a Λ) := by rw [ha']
            _ = Λ := by rw [← img_mul p M, inv_mul_cancel, img_one p M] }
    exact (Subgroup.closure_le K).2 (fun a ha => ha) hg
  · intro h
    exact Subgroup.subset_closure h

theorem span_img (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (Λ : Submodule (M p).L.O (Vp D p))
    (h : Submodule.span (D.s.atP p).Ep (Λ : Set (Vp D p)) = ⊤) :
    Submodule.span (D.s.atP p).Ep (LocNG.img g Λ : Set (Vp D p)) = ⊤ := by
  have himg : (LocNG.img g Λ : Set (Vp D p)) = (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p) '' (Λ : Set (Vp D p)) := by
    ext x
    simp [LocNG.img]
  rw [himg, Submodule.span_image, h, Submodule.map_top]
  exact LinearEquiv.range g

theorem img_key (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) : LocNG.img (c⁻¹ * g) A = B := by
  rw [img_mul p M, ← h2, h1, ← img_mul p M, inv_mul_cancel, img_one p M]

theorem img_key' (p : PlF D) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (c s g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (A B C : Submodule (M p).L.O (Vp D p))
    (h1 : C = LocNG.img c B) (h2 : C = LocNG.img g A) (h3 : LocNG.img s A = B) :
    LocNG.img ((c * s)⁻¹ * g) A = A := by
  rw [mul_inv_rev, mul_assoc, img_mul p M, img_key p M c g A B C h1 h2, ← h3, ← img_mul p M,
    inv_mul_cancel, img_one p M]

private theorem latP_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (hΛ : Submodule.IsLattice D.host.E Λ)
    (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hc : Submodule.IsLattice D.host.E (GlobalTheory.Unfold.LatLoc.cL Λ) :=
    GlobalTheory.Unfold.LatLoc.isLattice_map (GlobalTheory.Unfold.LatLoc.cE D) Λ hΛ
  have h := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (GlobalTheory.Unfold.LatLoc.cL Λ) hc).2.1 p
  rw [GlobalTheory.Unfold.LatLoc.localLattice_eq]
  exact h

private theorem gmap_inv_gmap_flag_measures (γ : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ L) = L := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hz' : (γ⁻¹ : GV D) (γ z) = z := γ.symm_apply_apply z
    rw [hz']
    exact hz
  · intro hx
    refine ⟨γ x, ⟨x, hx, rfl⟩, ?_⟩
    exact γ.symm_apply_apply x

end GlobalTheory.DblCos

open GlobalTheory.DblCos in
set_option maxHeartbeats 5000000 in

theorem GlobalTheory.DblCos.finite_double_cosets : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀
  obtain ⟨-, -, hLat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨-, Slat, hSlat⟩ := GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨hcmp, hglue⟩ := GlobalTheory.T.hermitianLattice_local_global_principle D Z

  let fam : LV D → ∀ p, ↥(FP p).UW0 := fun Λs p =>
    if hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
        lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ then ⟨hc.1.choose, hc.1.choose_spec.1⟩ else 1
  have fam_one : ∀ Λs p, lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀ → fam Λs p = 1 := by
    intro Λs p he
    simp only [fam]
    rw [dif_neg]
    exact fun hc => hc.2 he
  have fam_spec : ∀ Λs p, (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) →
      LocNG.img ((fam Λs p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀) =
        lattice₂ D Z.M p Λs := by
    intro Λs p hex
    by_cases he : lattice₂ D Z.M p Λs = lattice₂ D Z.M p Λ₀
    · rw [fam_one Λs p he, he]
      exact img_one p Z.M _
    · have hc : (∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs) ∧
          lattice₂ D Z.M p Λs ≠ lattice₂ D Z.M p Λ₀ := ⟨hex, he⟩
      simp only [fam, dif_pos hc]
      exact hc.1.choose_spec.2
  refine ⟨(Slat.filter (fun Λs => Submodule.IsLattice D.host.E Λs)).image fam, ?_, ?_⟩
  ·
    intro s hs
    obtain ⟨Λs, hmem, rfl⟩ := Finset.mem_image.1 hs
    have hL : Submodule.IsLattice D.host.E Λs := (Finset.mem_filter.1 hmem).2
    apply (hcmp Λs Λ₀ hL hΛ₀).1.subset
    intro p hp
    by_contra he
    apply hp
    rw [fam_one Λs p (not_not.1 he)]
    exact (mem_Aut_iff p Z.M _ _).2 (img_one p Z.M _)
  · intro g hg

    obtain ⟨Λ, hΛ, hΛp⟩ := hglue Λ₀ hΛ₀
      (fun p => LocNG.img ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
      (fun p => ⟨(latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p).1.map _, span_img p Z.M _ _ (latP_fg_and_span_eq_top Z Λ₀ hΛ₀ p).2⟩)
      (by
        apply hg.subset
        intro p hp hmem
        exact hp ((mem_Aut_iff p Z.M _ _).1 hmem))
    obtain ⟨Λs, hΛsS, γ, hγ, hγΛ⟩ := hSlat Λ hΛ (fun p => ⟨_, (g p).2, (hΛp p).symm⟩)
    have hΛsL : Submodule.IsLattice D.host.E Λs := by
      have := GlobalTheory.RatLocMove.isLattice_gmap' γ⁻¹ Λ hΛ
      rwa [← hγΛ, gmap_inv_gmap_flag_measures] at this
    let hh : ↥(FlagPairStabilizer F F') := ⟨γ, (mem_H0sub F F' γ).2 hγ⟩
    let s := fam Λs
    refine ⟨s, Finset.mem_image.2 ⟨Λs, Finset.mem_filter.2 ⟨hΛsS, hΛsL⟩, rfl⟩, hh,
      s⁻¹ * (φ hh)⁻¹ * g, ?_, by group⟩
    intro p

    have hC1 : lattice₂ D Z.M p Λ = LocNG.img ((φ hh p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)
        (lattice₂ D Z.M p Λs) := by
      rw [← hγΛ]
      exact hLat γ p _ Λs (hφ hh p)
    have hC2 := hΛp p
    have hex : ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λs :=
      ⟨(((φ hh p)⁻¹ * g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p), ((φ hh p)⁻¹ * g p).2, by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, img_mul p Z.M, ← hC2, hC1, ← img_mul p Z.M,
          inv_mul_cancel, img_one p Z.M]⟩
    have hs := fam_spec Λs p hex
    rw [mem_Aut_iff p Z.M]
    have key := img_key' p Z.M _ _ _ _ _ _ hC1 hC2 hs
    simpa [Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc] using key
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∃ S : Finset (∀ p, ↥(FP p).UW0), (∀ s ∈ S, {p | ((s p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite) ∧ ∀ g : ∀ p, ↥(FP p).UW0, {p | ((g p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → ∃ s ∈ S, ∃ h : ↥(FlagPairStabilizer F F'), ∃ k : ∀ p, ↥(FP p).UW0, (∀ p, ((k p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)) ∧ g = φ h * s * k := by
  atlas_forward_decl GlobalTheory.DblCos.finite_double_cosets
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.FixFin

section Img

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * g') Λ = LocNG.img g (LocNG.img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : LocNG.img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : LocNG.img g Λ = Λ') :
    LocNG.img g⁻¹ Λ' = Λ := by
  rw [← h, ← img_mul, inv_mul_cancel, img_one]

theorem mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg
    unfold LocNG.Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact img_one Λ
    | mul x y _ _ hx hy => rw [img_mul, hy, hx]
    | inv x _ hx => exact img_inv hx
  · intro h; exact Subgroup.subset_closure h

theorem img_fg_span (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  have e : (LocNG.img g L : Set V) = (g : V →ₗ[E] V) '' (L : Set V) := rfl
  rw [e, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

end Img

variable {D : D7}

theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) (LatLoc.isLattice_map _ _ h)).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

end GlobalTheory.Unfold.FixFin

set_option maxHeartbeats 1000000 in
open GlobalTheory.Unfold.FixFin in

theorem GlobalTheory.Unfold.FixFin.conj_aut_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ a ha
  have hLG := LatLoc.lattices_local_global D Z
  obtain ⟨Λa, hΛa, hΛap⟩ := hLG.2 Λ₀ hΛ₀
    (fun p => LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
    (fun p => img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p))
    (ha.subset fun p hp hA => hp (mem_Aut.1 hA))
  have H128 := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR
  have H133 := (GlobalTheory.T.rationalLatticeClasses_finite_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λa hΛa).1
  refine (H133.preimage Subtype.val_injective.injOn).subset ?_
  intro h hh
  refine ⟨h.2, ?_⟩
  have hgl : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λa) :=
    LatLoc.isLattice_map (h : GV D) Λa hΛa
  apply (hLG.1 _ _ hgl hΛa).2
  intro p
  rw [H128.2.2.1 (h : GV D) p _ Λa (hφ h p), hΛap p]
  have e := mem_Aut.1 (hh p)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, img_mul, img_mul] at e
  have e2 := congrArg (LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) e
  rwa [← img_mul, mul_inv_cancel, img_one] at e2
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  atlas_forward_decl GlobalTheory.Unfold.FixFin.conj_aut_finite
end

section
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocComm

theorem stab_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrel d τ hτ
  haveI := hM.loc
  haveI := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hk hrel
  obtain ⟨hUW, -, -, -, hAut, -⟩ := GlobalTheory.T.framePairCoordinates_transport_unitary_mass M hM H r k P S c
  obtain ⟨-, -, -, hStab, -⟩ := GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData M hM H r k P S c
  obtain ⟨hTC, -, -⟩ := GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver M hM H r k P S c
  have key : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.IsTerm (c.dat d) (c.lat τ.abelian₂) := fun d τ h => (hTC d τ h).1
  have eA : ∀ Λ, P.UW0 ⊓ LocNG.Aut Λ =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat Λ)).comap c.grp.toMonoidHom := by
    intro Λ
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rw [hUW, hAut]
  have eS : ∀ d : LocNG.Datum P, LocNG.Datum.Stab d =
      (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)).comap c.grp.toMonoidHom := by
    intro d
    ext g
    rw [Subgroup.mem_comap, hStab]
    rfl
  have rel : ∀ A B : Subgroup S.GLV,
      (A.comap c.grp.toMonoidHom).relIndex (B.comap c.grp.toMonoidHom) = A.relIndex B := by
    intro A B
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective c.grp.surjective]
  have fixd : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂) ≤ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d) := by
    intro d τ h x hx
    obtain ⟨hx0, hxs⟩ := Subgroup.mem_inf.mp hx
    have ht := key d τ h
    have h1 := (GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms M.L r k S _ _ ht x hx0).1
    rw [MulAction.mem_stabilizer_iff.mp hxs] at h1
    have h2 := (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ ht).2.2.2.2.2.2.2 _ h1
    exact Subgroup.mem_inf.mpr ⟨hx0, MulAction.mem_stabilizer_iff.mpr h2⟩
  have volH := GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement M.L r k S
  have cLam : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.lat τ.abelian₂)) := by
    intro d τ h
    have := volH.1 _ (GlobalTheory.T.hermitian_double_coset_term_basic_facts M.L r k S _ _ (key d τ h)).1.1
    exact ⟨this.1, this.2.1⟩
  have cDat : ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ →
      S.complementReferenceCompactSubgroup.Commensurable (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
    intro d τ h
    exact volH.2 _ _ (key d τ h)
  refine ⟨?_, ?_, ?_⟩
  · rw [eA, eS]
    exact Subgroup.comap_mono (fixd d τ hτ)
  · rw [eA, eS, rel]
    exact ((cLam d τ hτ).symm.trans (cDat d τ hτ)).1
  · intro d' τ' hτ'
    rw [eS, eS, rel]
    exact ((cDat d τ hτ).symm.trans (cDat d' τ' hτ')).1

end GlobalTheory.HL.LocComm
end

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTerm_stabilizer_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  atlas_forward_decl GlobalTheory.HL.LocComm.stab_commensurable
end

section
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StabLat

open Formalism.MainNotions.S.LocNG Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.BridgeLemma

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

theorem perpX_of (Fr : FrameD H r) {k : V} (h : ∀ a : Fin r, H.h k (Fr.f a.castSucc) = 0) :
    k ∈ H.perp (H.X Fr.f) := by
  intro x hx
  unfold HermSp.X at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact h a
  | zero => rw [H.h_herm 0 _, H.h_zero_left, map_zero]
  | add x y _ _ hx hy => rw [H.h_herm (x + y) _, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm, hx, hy, add_zero]
  | smul c x _ hx => rw [H.h_herm (c • x) _, H.h_smul_left, map_mul, ← H.h_herm, hx, mul_zero]

theorem e_mem_X (Fr : FrameD H r) (a : Fin r) : Fr.e a ∈ H.X Fr.f :=
  Submodule.subset_span ⟨a, rfl⟩

theorem sub_prF_mem (Fr : FrameD H r) {y : V} (hy : y ∈ H.perp (H.X Fr.f)) : y - Fr.prF y ∈ H.X Fr.f := by
  have h0 : ∀ a, H.h y (Fr.e a) = 0 := fun a => hy _ (e_mem_X Fr a)
  have e : y - Fr.prF y = ∑ a, H.h y (Fr.es a) • Fr.e a := by
    unfold FrameD.prF
    simp only [h0, zero_smul, Finset.sum_const_zero, sub_zero, sub_sub_cancel]
  rw [e]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (e_mem_X Fr a))

theorem prF_mem_perp (Fr : FrameD H r) (y : V) : Fr.prF y ∈ H.perp (H.X Fr.f) :=
  perpX_of Fr (fun a => ng_prF_e (Fr := Fr) y a)

theorem mkW_eq (Fr : FrameD H r) {x y : ↥(H.perp (H.X Fr.f))} (h : (x : V) - y ∈ H.X Fr.f) :
    H.mkW Fr.f x = H.mkW Fr.f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  exact h

theorem prF_mem_LamStd (Fr : FrameD H r) {L : Submodule M.L.O (H.Wb Fr.f)} {y : V}
    (hy : y ∈ H.perp (H.X Fr.f)) (hyL : H.mkW Fr.f ⟨y, hy⟩ ∈ L) : Fr.prF y ∈ Fr.LamStd L := by
  apply Submodule.subset_span
  refine ⟨fun a => ?_, fun a => ?_, ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩, rfl, ?_⟩
  · rw [ng_prF_es]; exact M.L.O.zero_mem
  · rw [ng_prF_e]; exact M.L.O.zero_mem
  · have e : H.mkW Fr.f ⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ = H.mkW Fr.f ⟨y, hy⟩ := by
      apply mkW_eq
      have h1 := sub_prF_mem Fr hy
      have h2 := sub_prF_mem Fr (prF_mem_perp Fr y)
      have : Fr.prF (Fr.prF y) - y = -((y - Fr.prF y) + (Fr.prF y - Fr.prF (Fr.prF y))) := by abel
      rw [show ((⟨Fr.prF (Fr.prF y), prF_mem_perp Fr _⟩ : ↥(H.perp (H.X Fr.f))) : V) = Fr.prF (Fr.prF y) from rfl,
        show ((⟨y, hy⟩ : ↥(H.perp (H.X Fr.f))) : V) = y from rfl, this]
      exact Submodule.neg_mem _ (Submodule.add_mem _ h1 h2)
    rw [e]; exact hyL

variable {P : FPair H r}

theorem h_add_right' (k u y : V) : H.h k (u + y) = H.h k u + H.h k y := by
  rw [H.h_herm (u + y) k, H.h_add_left, map_add, ← H.h_herm, ← H.h_herm]

theorem cls_mem {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V} (hk : k ∈ t.abelian₂)
    (hkp : k ∈ H.perp (H.X P.A.f)) : H.mkW P.A.f ⟨k, hkp⟩ ∈ d.L := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  refine ((d.hL.2.1 ⟨k, hkp⟩).2) (fun y hyL => ?_)
  have hy := y.2
  have hyL' : H.mkW P.A.f ⟨(y : V), hy⟩ ∈ d.L := hyL
  have h0 := prF_mem_LamStd P.A hy hyL'
  have hny : n (P.A.prF y) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  have hint := ng_term_int ht hk hny
  have hu : n (P.A.prF y) - y ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A (y : V))
    have h2 := sub_prF_mem P.A hy
    have : n (P.A.prF y) - y = (n (P.A.prF y) - P.A.prF y) - ((y : V) - P.A.prF y) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have e : n (P.A.prF y) = (n (P.A.prF y) - y) + y := by abel
  rw [e, h_add_right', hkp _ hu, zero_add] at hint
  exact hint

theorem mem_of_cls (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {k : V}
    (ho : NgOrth P k) (hkL : H.mkW P.A.f ⟨k, ng_orth_perp P.A ho.1⟩ ∈ d.L) : k ∈ t.abelian₂ := by
  have ht' := ht
  obtain ⟨_, _, ⟨n, hn, -, hL⟩, _, _⟩ := ht'
  have hN := mem_NSet_of_mem_N P.A hn
  have hkp := ng_orth_perp P.A ho.1
  have h0 := prF_mem_LamStd P.A hkp hkL
  have hny : n (P.A.prF k) ∈ t.abelian₂ := by rw [hL]; exact ⟨_, h0, rfl⟩
  obtain ⟨m0, hm0, hk', hko⟩ := ng_term_split hP ht hny
  have hXle : H.X P.A.f ≤ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl a.castSucc, rfl⟩
  have hx : n (P.A.prF k) - k ∈ H.X P.A.f := by
    have h1 := hN.2.2 _ (prF_mem_perp P.A k)
    have h2 := sub_prF_mem P.A hkp
    have : n (P.A.prF k) - k = (n (P.A.prF k) - P.A.prF k) - (k - P.A.prF k) := by abel
    rw [this]; exact Submodule.sub_mem _ h1 h2
  have hz : k - (n (P.A.prF k) - m0) = 0 := by
    refine ng_zero (H := H) (Sum.elim P.A.f P.B.f) ?_ ?_ ?_
    · rw [ng_gram_base]
      exact IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (ng_G_unit (by
        intro h0
        obtain ⟨_, y, _, hy⟩ := hP.2.1
        rw [h0, zero_mul] at hy
        have := Formalism.MainNotions.LocalModelPeriodLattices.nontrivial_E M.L
        exact zero_ne_one hy))
    · have e : k - (n (P.A.prF k) - m0) = m0 - (n (P.A.prF k) - k) := by abel
      rw [e]
      exact Submodule.sub_mem _ (ng_span_base ht hm0) (hXle hx)
    · rintro (b | b)
      · rw [Sum.elim_inl, h_sub_left, ho.1, hko.1, sub_zero]
      · rw [Sum.elim_inr, h_sub_left, ho.2, hko.2, sub_zero]
  rw [sub_eq_zero.1 hz]; exact hk'

theorem complementUnitary_isUnitary_fixes_frames {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    have e : ∀ u, x ((x⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply x u
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · rw [← hx.1, e, e]
    · conv_lhs => rw [← (hx.2 b).1]
      exact LinearEquiv.symm_apply_apply x _
    · conv_lhs => rw [← (hx.2 b).2]
      exact LinearEquiv.symm_apply_apply x _

theorem img_le (hP : P.PrimeTo) {d : Datum P} {t : Term V M r} (ht : IsTermOver P d t) {g : V ≃ₗ[E] V}
    (hU : IsUnitary H g) (hfix : ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b)
    (hmov : ∀ x y : ↥(H.perp (H.X P.A.f)), (y : V) = g x → H.mkW P.A.f x ∈ d.L → H.mkW P.A.f y ∈ d.L) :
    img g t.abelian₂ ≤ t.abelian₂ := by
  have hf := ng_term_f ht
  have hM : Submodule.span M.L.O (Set.range (Sum.elim t.f t.f')) ≤ t.abelian₂ := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with b | b
    · exact (hf b).1
    · exact (hf b).2
  have hfixME : ∀ x ∈ Submodule.span E (Set.range (Sum.elim P.A.f P.B.f)), g x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rcases j with b | b
      · exact (hfix b).1
      · exact (hfix b).2
    | zero => exact map_zero g
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨m0, hm0, hk, hko⟩ := ng_term_split hP ht hv
  show g v ∈ t.abelian₂
  have e : g v = m0 + g (v - m0) := by
    rw [map_sub, hfixME m0 (ng_span_base ht hm0)]; abel
  rw [e]
  refine t.abelian₂.add_mem (hM hm0) ?_
  have hgo : NgOrth P (g (v - m0)) := by
    constructor
    · intro b; rw [← (hfix b).1, hU, hko.1]
    · intro b; rw [← (hfix b).2, hU, hko.2]
  apply mem_of_cls hP ht hgo
  exact hmov ⟨v - m0, ng_orth_perp P.A hko.1⟩ _ rfl (cls_mem ht hk _)

theorem stab_le_aut : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Stab d ≤ LocNG.Aut τ.abelian₂ := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r k P _ _ hP d τ ht
  unfold Datum.Stab
  rw [Subgroup.closure_le]
  rintro g ⟨hg, hmv⟩
  obtain ⟨hU, hfix⟩ := complementUnitary_isUnitary_fixes_frames hg
  rw [SetLike.mem_coe, ng_mem_Aut]
  have e : ∀ u, g ((g⁻¹ : V ≃ₗ[E] V) u) = u := fun u => LinearEquiv.apply_symm_apply g u
  have h1 := img_le hP ht hU hfix (fun x y hxy hx => (hmv.1 x y hxy).1 hx)
  have hU' : IsUnitary H g⁻¹ := fun u v => by rw [← hU, e, e]
  have hfix' : ∀ b, (g⁻¹ : V ≃ₗ[E] V) (P.A.f b) = P.A.f b ∧ (g⁻¹ : V ≃ₗ[E] V) (P.B.f b) = P.B.f b := fun b => by
    constructor
    · conv_lhs => rw [← (hfix b).1]
      exact LinearEquiv.symm_apply_apply g _
    · conv_lhs => rw [← (hfix b).2]
      exact LinearEquiv.symm_apply_apply g _
  have h2 := img_le hP ht hU' hfix' (fun x y hxy hx => by
    refine (hmv.1 y x ?_).2 hx
    rw [hxy]; exact (e x).symm)
  refine le_antisymm h1 ?_
  have h3 := ng_img_mono g h2
  rwa [← ng_img_mul, mul_inv_cancel, ng_img_one] at h3

end GlobalTheory.HL.StabLat
end

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datumStabilizer_preserves_termLattice_goodPlace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → P.PrimeTo → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → LocNG.Datum.Stab d ≤ LocNG.Aut τ.abelian₂ := by
  atlas_forward_decl GlobalTheory.HL.StabLat.stab_le_aut
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Unfold.LocStab

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have := D.R.two_le_m; obtain ⟨t, ht⟩ := D.R.m_even
  unfold Ranks.rS Ranks.r; omega

theorem relIndex_comap_subtype {G : Type*} [Group G] (U X Y : Subgroup G) (hY : Y ≤ U) :
    (X.comap U.subtype).relIndex (Y.comap U.subtype) = X.relIndex Y := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hY]

theorem stabilizer_eq_comap {G α : Type*} [Group G] (U : Subgroup G) [MulAction U α] (S : Subgroup G) (d : α)
    (h : ∀ g : U, g.1 ∈ S ↔ g • d = d) : MulAction.stabilizer U d = S.comap U.subtype := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.coe_subtype, h g]

theorem comap_subtype_inf {G : Type*} [Group G] (U A : Subgroup G) :
    (U ⊓ A).comap U.subtype = A.comap U.subtype := by
  ext g; simp

end GlobalTheory.Unfold.LocStab

namespace GlobalTheory.Unfold.LocStab

set_option maxHeartbeats 1000000 in

theorem local_stabilisers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel _ hMv hSt Λ₀ d0 hLO
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hstab : ∀ p (d : LocNG.Datum (FP p)),
      MulAction.stabilizer ↥(FP p).UW0 d = (LocNG.Datum.Stab d).comap (FP p).UW0.subtype :=
    fun p d => stabilizer_eq_comap _ _ d (fun g => hSt p d g)
  have hle : ∀ p (d : LocNG.Datum (FP p)), LocNG.Datum.Stab d ≤ (FP p).UW0 :=
    fun p d => Subgroup.closure_le _ |>.2 fun g hg => hg.1
  choose τ0 hτ0 hτ0L using hLO.2
  have hc := fun p => GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
    (hRel p) (d0 p) (τ0 p) (hτ0 p)
  have hA : ∀ p, (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype =
      ((FP p).UW0 ⊓ LocNG.Aut (τ0 p).abelian₂).comap (FP p).UW0.subtype := by
    intro p; rw [comap_subtype_inf, hτ0L p]
  refine ⟨fun p => ?_, ?_, fun d hd p => ?_⟩
  · rw [hA p, hstab p]
    refine ⟨?_, ?_⟩
    · rw [relIndex_comap_subtype _ _ _ inf_le_left, Subgroup.relIndex_eq_one.2 (hc p).1]
      exact one_ne_zero
    · rw [relIndex_comap_subtype _ _ _ (hle p (d0 p))]
      exact (hc p).2.1
  · have hAt : ∀ p, GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') (FP p) := fun p => by
      obtain ⟨h1, h2, h3, h4⟩ := hB p
      exact ⟨h1, h2, h3, h4⟩
    refine (GlobalTheory.T.finite_places_not_primeTo_baseFrameInvariants D Z u u' F F' hG FP hAt).subset fun p hp hpr => hp ?_
    have h2 := GlobalTheory.T.datumStabilizer_preserves_termLattice_goodPlace (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) hpr (d0 p) (τ0 p) (hτ0 p)
    rw [hA p, hstab p]
    exact congrArg _ (le_antisymm (hc p).1 (le_inf (hle p (d0 p)) h2))
  · obtain ⟨τ, hτ⟩ := hd p
    have h3 := (hc p).2.2
    have hτc := GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) (d p) τ hτ
    rw [hstab p, hstab p, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p))]
    refine ⟨h3 (d p) τ hτ, hτc.2.2 (d0 p) (τ0 p) (hτ0 p), ?_⟩
    rw [GlobalTheory.HL.invVol, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p)), LocNG.Datum.wt, LocNG.volRel, one_div_div]

end GlobalTheory.Unfold.LocStab
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  atlas_forward_decl GlobalTheory.Unfold.LocStab.local_stabilisers
end

section
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Unfold.massA_eq_sum_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ _hinj _inst hmov d

  have huniq := (GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR).1

  have key : ∀ (h : ↥(FlagPairStabilizer F F')) (y y' : Dat Z FP),
      RMoves h.1 y y' ↔ (fun p => φ h p • y p) = y' := by
    intro h y y'
    constructor
    · intro hm
      funext p
      obtain ⟨g', hg', hmv⟩ := hm p
      have he : g' = ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
        (huniq h.1 p).unique hg' (hφ h p)
      subst he
      exact (hmov p (φ h p) (y p) (y' p)).1 hmv
    · intro he p
      exact ⟨_, hφ h p, (hmov p (φ h p) (y p) (y' p)).2 (congrFun he p)⟩

  have hrel : GRel (Z := Z) (FP := FP) F F' =
      (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y') := by
    funext y y'
    apply propext
    constructor
    · rintro ⟨h, hh, hm⟩
      exact ⟨⟨h, (mem_H0sub F F' h).2 hh⟩, (key ⟨h, (mem_H0sub F F' h).2 hh⟩ y y').1 hm⟩
    · rintro ⟨h, hh⟩
      exact ⟨h.1, (mem_H0sub F F' h.1).1 h.2, (key h y y').2 hh⟩

  have hstab : ∀ y : Dat Z FP, (stabY F F' y).encard =
      {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y}.encard := by
    intro y
    have hs : stabY F F' y = Subtype.val '' {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y} := by
      ext g
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, (mem_H0sub F F' g).2 hg⟩, (key ⟨g, (mem_H0sub F F' g).2 hg⟩ y y).1 hm, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(mem_H0sub F F' h.1).1 h.2, (key h y y).2 hh⟩
    rw [hs, Subtype.val_injective.encard_image]
  rw [massA, hrel]
  refine tsum_congr fun o => ?_

  have hin : InGen d o.out ↔
      (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite := by
    unfold InGen
    refine and_congr (forall_congr' fun p => ?_) Iff.rfl
    constructor
    · rintro ⟨g, hg, hm⟩
      exact ⟨⟨g, hg⟩, (hmov p ⟨g, hg⟩ (d p) (o.out p)).1 hm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.1, g.2, (hmov p g (d p) (o.out p)).2 hg⟩
  by_cases hc : (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite
  · rw [if_pos (hin.2 hc), if_pos hc, hstab]
  · rw [if_neg (mt hin.1 hc), if_neg hc]
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  atlas_forward_decl GlobalTheory.Unfold.massA_eq_sum_orbits
end

section
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HL

namespace GlobalTheory.Unfold

theorem mass_genus_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR d0 hd0 hΛ
  obtain ⟨φ, hφi, hφE⟩ := GlobalTheory.T.frameFixingIsometries_embed_prod_localUnitary D X Y u u' F F' w hw hG Z FP hB hR
  obtain ⟨Λ₀, hLO⟩ := GlobalTheory.T.exists_globalLattice_over_localInnerData D Z FP d0 hd0 hΛ
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    intro p
    have hm : D.R.m = 2 * D.R.rS + 2 := by
      have := D.R.two_le_m; obtain ⟨a, ha⟩ := D.R.m_even; unfold Ranks.rS; omega
    rw [finrank_Vp]; unfold Ranks.r; omega
  have hact : ∀ p : PlF D, ∃ act : MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)),
      (∀ (g : ↥(FP p).UW0) d d', LocNG.Datum.Moves g.1 d d' ↔ act.smul g d = d') ∧
      ∀ d (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ act.smul g d = d :=
    fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (hrk p) (hR p)
  choose act hMv hSt using hact
  letI : ∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p)) := act
  have hMv' : ∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d' := hMv
  have hSt' : ∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d := hSt
  obtain ⟨hc0, hfin, hdd⟩ := GlobalTheory.T.localLatticeStabilisers_commensurable_almostEverywhere D X Y u u' F F' w hw hG Z FP hB hR hMv' hSt' Λ₀ d0 hLO
  have hlat : Submodule.IsLattice D.host.E Λ₀ := hLO.1
  obtain ⟨V1, hV1, hmain⟩ := GlobalTheory.T.mass_genus_restricted_product (fun p => ↥(FP p).UW0) (fun p => LocNG.Datum (FP p))
    (fun p => (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ↥(FlagPairStabilizer F F') φ hφi
    (GlobalTheory.T.frameFixingIsometry_ext_preserves_completions_ae D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat)
    (GlobalTheory.T.finite_doubleCosets_rational_localLatticeStabilizers D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat)
    (GlobalTheory.T.finite_rationalIsometries_fixing_frames_conjStabilizer D X Y u u' F F' w hw hG Z FP hB hR φ hφE Λ₀ hlat) d0 hc0 hfin
  refine ⟨V1, hV1, fun d hd hfd => ?_⟩
  have h3 := hdd d hd
  rw [GlobalTheory.T.genusMass_eq_sum_over_rationalGroup_orbits D X Y u u' F F' w hw hG Z FP hB hR φ hφE hφi hMv' d]
  have hm2 := hmain d (fun p => ⟨(h3 p).1, (h3 p).2.1⟩) hfd
  have e : (∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) = ∏ᶠ p, invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) := finprod_congr fun p => ((h3 p).2.2).symm
  refine hm2.trans ?_
  rw [e]

end GlobalTheory.Unfold
end
end

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_genus_local_data_product_local_weights : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ d0 : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ {p | ¬ ∃ τ, LocNG.IsTermOver (FP p) (d0 p) τ ∧ τ.abelian₂ = lattice₂ D Z.M p Λ₀}.Finite) → ∃ V1 : ℝ, 0 < V1 ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → {p | d p ≠ d0 p}.Finite → massA F F' d = ENNReal.ofReal (V1 * ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p)) := by
  atlas_forward_decl GlobalTheory.Unfold.mass_genus_local_weights
end
