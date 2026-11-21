import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGlob
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarGenLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmLocPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarOmPart
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarNMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdN
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrGlobOfFstar
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowLatOfMove
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LastCoordMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AdmissibleLocalPartner
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdBetaRep

section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem ident_generic {r : ℕ} (Lam₁ Lam₂ : Submodule M.L.O V) (f₀ f₁ f₂ : Fin (r + 1) → V) (T T' : F)
    (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁)
    (hX0 : ∀ a ∈ H.X f₀, ∀ b ∈ H.X f₀, H.h a b = 0) (hX2 : ∀ a ∈ H.X f₂, ∀ b ∈ H.X f₂, H.h a b = 0)
    (hW0 : ∀ w ∈ H.W0 f₀ f₁, ∃ w₂ ∈ H.W0 f₀ f₂, w - w₂ ∈ H.X f₀ ∧ e w - w₂ ∈ H.X f₂)
    (homp : H.Dl f₀ f₂ (r + 1) • H.om' f₀ f₁ - H.Dl f₀ f₁ (r + 1) • H.om' f₀ f₂ ∈ H.X f₀)
    (hom : M.L.cj (H.Dl f₀ f₂ (r + 1)) • e (H.om f₀ f₁) - M.L.cj (H.Dl f₀ f₁ (r + 1)) • H.om f₀ f₂ ∈ H.X f₂)
    (hrat : H.Dl f₀ f₁ r * H.Dl f₀ f₂ (r + 1) = H.Dl f₀ f₂ r * H.Dl f₀ f₁ (r + 1))
    (hz : e (f₁ (Fin.last r)) - f₂ (Fin.last r) ∈ H.X f₂) :
    H.Ident (⟨Lam₁, f₀, f₁, T, T'⟩ : Loc.Term V M r) ⟨Lam₂, f₀, f₂, T, T'⟩ (LinearEquiv.refl _ _)
        (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) ∧
      H.SendsTo (qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).toLinearMap 1 1 (f₁ (Fin.last r)) (f₂ (Fin.last r)) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, hrat⟩, ?_⟩
  · intro x y x₂ y₂ hx hy
    exact h_eq_of_sub_mem H _ hX0 x.2 y.2 ((mk_eq_iff H _ x x₂).1 hx) ((mk_eq_iff H _ y y₂).1 hy)
  · intro x y x₂ y₂ hx hy
    have hx' : e x - x₂ ∈ H.X f₂ := (mk_eq_iff H _ _ x₂).1 hx
    have hy' : e y - y₂ ∈ H.X f₂ := (mk_eq_iff H _ _ y₂).1 hy
    rw [h_eq_of_sub_mem H _ hX2 (perp_map H e hiso _ _ h21 x.2) (perp_map H e hiso _ _ h21 y.2) hx' hy',
      hiso]
  · intro w hw
    obtain ⟨w₂, hw₂, h1, h2⟩ := hW0 w hw
    refine ⟨w₂, hw₂, ?_, ?_⟩
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      rw [one_smul, one_smul, hx, hx₂]
      exact h1
    · intro x x₂ hx hx₂
      apply smul_mk_eq H
      show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
      rw [one_smul, one_smul, hx, hx₂]
      exact h2
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    rw [hx, hx₂]
    exact homp
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show M.L.cj (H.Dl f₀ f₂ (r + 1)) • e x - M.L.cj (H.Dl f₀ f₁ (r + 1)) • (x₂ : V) ∈ H.X f₂
    rw [hx, hx₂]
    exact hom
  · intro x x₂ hx hx₂
    apply smul_mk_eq H
    show (1 : E) • e x - (1 : E) • (x₂ : V) ∈ H.X f₂
    rw [one_smul, one_smul, hx, hx₂]
    exact hz

end Generic

section Concrete

variable {D : D7} (Zd : LocDat D) (p : PlF D)

theorem omp_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (P K : (D.s.atP p).Ep) :
    (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g1)) -
      (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom' f g2)) =
    (P * K) • baseChange₂ D p (GDl f g2 (D.R.rS + 1) • Gom' f g1 - GDl f g1 (D.R.rS + 1) • Gom' f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 2 <;> ring

theorem om_combine' (f g1 g2 : Fin (D.R.rS + 1) → (VS D).V) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (P K : (D.s.atP p).Ep) :
    (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g2 (D.R.rS + 1))) • (K • baseChange₂ D p (β (Gom f g1))) -
      (Zd.M p).L.cj (P * (D.s.atP p).ιE (GDl f g1 (D.R.rS + 1))) • (K • baseChange₂ D p (Gom f g2)) =
    ((Zd.M p).L.cj P * K) • baseChange₂ D p (star (GDl f g2 (D.R.rS + 1)) • β (Gom f g1) -
      star (GDl f g1 (D.R.rS + 1)) • Gom f g2) := by
  rw [map_sub, baseChange_smul₂, baseChange_smul₂, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, map_mul, map_mul,
    cj_iota (Zd.hcj p), cj_iota (Zd.hcj p)]
  congr 2 <;> ring

theorem betaP_fix {ι : Type} [Fintype ι] (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (u y : ι → (VS D).V)
    (hform : ∀ v, g v = v + ∑ k, (VS D).hT (u k) v • y k) (w : Vp D p)
    (hw : ∀ k, (locH Zd p).h w (baseChange₂ D p (u k)) = 0) : betaP p g w = w := by
  have hk : ∀ k, ∑ i, w i * (D.s.atP p).ιE ((VS D).hT (u k) ((VS D).frame i)) = 0 := by
    intro k
    have e := hw k
    conv_lhs at e => rw [vp_eq_sum p w]
    rw [h_sum_left] at e
    rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermitian_base_change_smul Zd p]
    rfl
  conv_lhs => rw [vp_eq_sum p w]
  rw [map_sum]
  simp only [map_smul, betaP_bc, hform, map_add, baseChangeAt_sum, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul]
  rw [← vp_eq_sum p w, Finset.sum_comm]
  simp only [← Finset.sum_smul, hk, zero_smul, Finset.sum_const_zero, add_zero]

theorem gdl_eq (f g : Fin (D.R.rS + 1) → (VS D).V) (l : ℕ) : GDl f g l = leadMinorE (starZh f g) l := by
  unfold GDl leadMinorE
  split_ifs <;> rfl

theorem xspan_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => F.fvec a.castSucc) = F.X := by
  have : (fun a : Fin D.R.rS => F.fvec a.castSucc) = F.e := funext fun a => by simp [FlagG.fvec]
  rw [this]; rfl

end Concrete

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

def StarIdentU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    (∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)) →
    ∀ F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z → starCompat γ F'₂ →
      starInU γ F'₂ →
      ∀ p, ∃ φ' : (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂),
        LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _) φ'

def StarFrameU : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D), Ctx γ Z →
    ∃ F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), ZhatL (lf D F0) F'₂ = Z ∧ starCompat γ F'₂ ∧
      starInU γ F'₂

variable {u u' F0 what₂}

theorem starFrameU_holds : StarFrameU u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨hZ, hZ₁, hx⟩ := starMinors_holds u u' F0 what₂ γ Z hC
  obtain ⟨h1, h2⟩ := star_frame_orthogonal γ
  obtain ⟨F₂, hZh, hom, hsp⟩ := FsLA.frame_la F0 (starFrame γ) h1 h2 Z hZ hZ₁ hx
  refine ⟨⟨F₂, F₂.z⟩, hZh, ⟨?_, ?_⟩, fun b => hsp b⟩
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z := hZh
    rw [e, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    exact hx
  · have e : starZh (frame (lf D F0)) (frame (⟨F₂, F₂.z⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))) = Z := hZh
    rw [FsLA.leadMinorE_full, FsLA.leadMinorE_full, e]
    exact hom

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Zd : LocDat D)

theorem localLattice_preserves_cofinite (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) :
    {p : PlF D | ¬ ∀ x ∈ lattice₂ D Zd.M p Λ, betaP p g x ∈ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨s, hs⟩ := hΛ.fg
  refine (s.finite_toSet.biUnion fun v _ => CohIntPf.bcP_mem_cof Zd hΛ (g v)).subset ?_
  intro p hp
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  by_contra hall
  push_neg at hall
  apply hp
  have hloc : ∀ v ∈ Λ, g v ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ := by
    intro v hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ _).1 (hall v hv)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx =>
      rw [show g (o • x) = o • g x from (g : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower o x]
      exact Submodule.smul_mem _ _ hx
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [betaP_bc]
    exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ _).2 (hloc v hv)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ _ hx

theorem localLattice_preserves_cofinite_symm (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsLattice D.host.E Λ) :
    {p : PlF D | ¬ ∀ x ∈ lattice₂ D Zd.M p Λ, (betaP p g).symm x ∈ lattice₂ D Zd.M p Λ}.Finite := by
  obtain ⟨s, hs⟩ := hΛ.fg
  refine (s.finite_toSet.biUnion fun v _ => CohIntPf.bcP_mem_cof Zd hΛ (g.symm v)).subset ?_
  intro p hp
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  by_contra hall
  push_neg at hall
  apply hp
  have hloc : ∀ v ∈ Λ, g.symm v ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ := by
    intro v hv
    rw [← hs] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ _).1 (hall v hv)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx =>
      rw [show g.symm (o • x) = o • g.symm x from
        (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower o x]
      exact Submodule.smul_mem _ _ hx
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [betaP_symm_bc]
    exact (Formalism.L2.SG.Pf.LocalDenominators.baseChangeAt_mem_localLattice_iff Zd p hΛ _).2 (hloc v hv)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ _ hx

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem lset_map {r : ℕ} (f₁ f₂ : Fin (r + 1) → V) (e : V ≃ₗ[E] V) (hiso : ∀ v w, H.h (e v) (e w) = H.h v w)
    (h12 : ∀ x ∈ H.X f₁, e x ∈ H.X f₂) (h21 : ∀ y ∈ H.X f₂, e.symm y ∈ H.X f₁) (abelian₂ : Submodule M.L.O V)
    (hL : ∀ x ∈ abelian₂, e x ∈ abelian₂) (hL' : ∀ x ∈ abelian₂, e.symm x ∈ abelian₂) :
    ⇑(qEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21) '' H.Lset abelian₂ f₁ = H.Lset abelian₂ f₂ := by
  ext w
  simp only [Set.mem_image]
  constructor
  · rintro ⟨w0, ⟨x, hxL, rfl⟩, rfl⟩
    refine ⟨perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21 x, hL _ hxL, ?_⟩
    exact (qEquiv_mk H e hiso _ _ h12 h21 x).symm
  · rintro ⟨y, hyL, rfl⟩
    refine ⟨H.mkW f₁ ((perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y),
      ⟨(perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y, ?_, rfl⟩, ?_⟩
    · have hy : (((perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y : ↥(H.perp (H.X f₁))) : V) =
          e.symm y := by
        simp [perpEquiv, LinearEquiv.ofSubmodules_symm_apply]
      rw [hy]
      exact hL' _ hyL
    · show qEquiv H e hiso _ _ h12 h21
          (Submodule.Quotient.mk ((perpEquiv H e hiso (H.X f₁) (H.X f₂) h12 h21).symm y)) =
        Submodule.Quotient.mk y
      rw [qEquiv_mk, LinearEquiv.apply_symm_apply]

end Generic

section Concrete

variable {D : D7} (Zd : LocDat D) (p : PlF D)

theorem local_beta_mem_x (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f₁ f₂ : Fin (D.R.rS + 1) → (VS D).V)
    (hg1 : ∀ b, g (f₁ b) = f₂ b) :
    ∀ x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)),
      betaP p g x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
  intro x hx
  refine betaP_mem_X (Z := Zd) (p := p) g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p) ?_ hx
  intro a
  rw [hg1]
  exact Submodule.subset_span ⟨a, rfl⟩

theorem local_beta_symm_mem_x (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (f₁ f₂ : Fin (D.R.rS + 1) → (VS D).V)
    (hg1 : ∀ b, g (f₁ b) = f₂ b) :
    ∀ x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)),
      (betaP p g).symm x ∈ (locH Zd p).X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) := by
  intro x hx
  refine betaP_symm_mem_X (Z := Zd) (p := p) g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p) ?_ hx
  intro a
  rw [← hg1, LinearEquiv.symm_apply_apply]
  exact Submodule.subset_span ⟨a, rfl⟩

def starPhi (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hiso : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y)
    (f₁ f₂ : Fin (D.R.rS + 1) → (VS D).V) (hg1 : ∀ b, g (f₁ b) = f₂ b) :
    (locH Zd p).Wb (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) ≃ₗ[(D.s.atP p).Ep]
      (locH Zd p).Wb (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) :=
  qEquiv (locH Zd p) (betaP p g) (betaP_iso Zd p g hiso) _ _ (local_beta_mem_x Zd p g f₁ f₂ hg1) (local_beta_symm_mem_x Zd p g f₁ f₂ hg1)

end Concrete

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.FsLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

set_option maxHeartbeats 1000000 in

theorem starIdentG (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) (hC : Ctx γ Z)
    (hgen : ∀ p, (locH Zd p).IsGeneric (tLoc Zd p γ)) (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hZ : ZhatL (lf D F0) F'₂ = Z) (hc : starCompat γ F'₂) (hU : starInU γ F'₂)
    (g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (y : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → (VS D).V)
    (hiso : ∀ x x', (VS D).hT (g x) (g x') = (VS D).hT x x') (hg1 : ∀ b, g (starFrame γ b) = frame F'₂ b)
    (hform : ∀ v, g v = v + ∑ k, (VS D).hT (Sum.elim (frame (lf D F0)) (starFrame γ) k) v • y k)
    (hom : star (starZh (frame (lf D F0)) (starFrame γ)).det • starOmL (frame (lf D F0)) (frame F'₂) -
        star Z.det • g (starOmL (frame (lf D F0)) (starFrame γ)) ∈ Xsp F'₂) (p : PlF D) :
    LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (LinearEquiv.refl _ _)
      (FsLoc.starPhi Zd p g hiso (starFrame γ) (frame F'₂) hg1) := by
  set f := frame (lf D F0) with hf
  set f₁ := starFrame γ with hf₁
  set f₂ := frame F'₂ with hf₂
  set H := locH Zd p with hH
  set e := betaP p g with he
  have hisoL : ∀ v w, H.h (e v) (e w) = H.h v w := betaP_iso Zd p g hiso
  have hgs : ∀ b, g.symm (f₂ b) = f₁ b := fun b => by rw [← hg1 b, LinearEquiv.symm_apply_apply]
  have h12 : ∀ x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)), e x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) :=
    fun x hx => betaP_mem_X Zd p g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p)
      (fun a => by rw [hg1]; exact Submodule.subset_span ⟨a, rfl⟩) hx
  have h21 : ∀ x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)), e.symm x ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) :=
    fun x hx => betaP_symm_mem_X Zd p g f₁ f₂ (sF' Zd p) (isUnit_sF' Zd p)
      (fun a => by rw [hgs]; exact Submodule.subset_span ⟨a, rfl⟩) hx
  have hX0 : ∀ a ∈ H.X (fun a => sF Zd p a • baseChange₂ D p (f a)), ∀ b ∈ H.X (fun a => sF Zd p a • baseChange₂ D p (f a)),
      H.h a b = 0 := by
    apply iso_span
    intro i j
    rw [h_bcP, brS, show (VS D).hT (f j.castSucc) (f i.castSucc) = 0 from
      FsLA.gram_fvec_zero F0 _ _ (Or.inl (Fin.castSucc_lt_last j).ne), map_zero, mul_zero]
  have hX2 : ∀ a ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)), ∀ b ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)),
      H.h a b = 0 := by
    apply iso_span
    intro i j
    rw [h_bcP, brS, show (VS D).hT (f₂ j.castSucc) (f₂ i.castSucc) = 0 from
      FsLA.gram_fvec_zero F'₂.fl _ _ (Or.inl (Fin.castSucc_lt_last j).ne), map_zero, mul_zero]
  have hW0 : ∀ w ∈ H.W0 (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)),
      ∃ w₂ ∈ H.W0 (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)),
        w - w₂ ∈ H.X (fun a => sF Zd p a • baseChange₂ D p (f a)) ∧
        e w - w₂ ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
    intro w hw
    rw [mem_orthogonal_frame_iff] at hw
    have hperp : ∀ k, H.h w (baseChange₂ D p (Sum.elim f f₁ k)) = 0 := by
      rintro (a | b)
      · exact h_zero_of_smul Zd p (isUnit_sF Zd p a) (hw.1 a)
      · exact h_zero_of_smul Zd p (isUnit_sF' Zd p b) (hw.2 b)
    have hew : e w = w := FsLoc.betaP_fix Zd p g _ y hform w hperp
    refine ⟨w, ?_, by rw [sub_self]; exact Submodule.zero_mem _, by rw [hew, sub_self]; exact Submodule.zero_mem _⟩
    rw [mem_orthogonal_frame_iff]
    refine ⟨hw.1, fun b => ?_⟩
    have hb : baseChange₂ D p (f₂ b) ∈ Submodule.span (D.s.atP p).Ep (Set.range fun k => baseChange₂ D p (Sum.elim f f₁ k)) :=
      baseChange_mem_span p _ (hU b)
    have hwp : w ∈ H.perp (Submodule.span (D.s.atP p).Ep (Set.range fun k => baseChange₂ D p (Sum.elim f f₁ k))) := by
      rw [mem_perp_span]; rintro _ ⟨k, rfl⟩; exact hperp k
    show H.h w (sF' Zd p b • baseChange₂ D p (f₂ b)) = 0
    rw [h_smul_right, hwp _ hb, mul_zero]
  have hglob : GDl f f₂ (D.R.rS + 1) • Gom' f f₁ - GDl f f₁ (D.R.rS + 1) • Gom' f f₂ ∈
      Submodule.span D.host.E (Set.range fun a : Fin D.R.rS => f a.castSucc) := by
    rw [FsLoc.gdl_eq, FsLoc.gdl_eq, FsLoc.xspan_eq F0]
    exact hc.2
  have homp : H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) (D.R.rS + 1) •
        H.om' (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) -
      H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) (D.R.rS + 1) •
        H.om' (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) ∈
      H.X (fun a => sF Zd p a • baseChange₂ D p (f a)) := by
    rw [om'_loc, om'_loc, dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ le_rfl,
      dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ le_rfl, FsLoc.omp_combine' p]
    exact Submodule.smul_mem _ _ (bcP_mem_X Zd p f (sF Zd p) (isUnit_sF Zd p) hglob)
  have hglob2 : star (GDl f f₂ (D.R.rS + 1)) • g (Gom f f₁) - star (GDl f f₁ (D.R.rS + 1)) • Gom f f₂ ∈
      Submodule.span D.host.E (Set.range fun b : Fin D.R.rS => f₂ b.castSucc) := by
    rw [FsLoc.gdl_eq, FsLoc.gdl_eq, FsLoc.xspan_eq F'₂.fl, FsLA.leadMinorE_full, FsLA.leadMinorE_full]
    have hn := Submodule.neg_mem _ hom
    rw [neg_sub] at hn
    have hZe : starZh f f₂ = Z := hZ
    rw [hZe]
    exact hn
  have hom' : (Zd.M p).L.cj (H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b))
        (D.R.rS + 1)) • e (H.om (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b))) -
      (Zd.M p).L.cj (H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b))
        (D.R.rS + 1)) • H.om (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) ∈
      H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
    rw [om_loc, om_loc, dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ le_rfl,
      dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ le_rfl, map_smul, betaP_bc, FsLoc.om_combine' Zd p]
    exact Submodule.smul_mem _ _ (bcP_mem_X Zd p f₂ (sF' Zd p) (isUnit_sF' Zd p) hglob2)
  have hrat : H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) D.R.rS *
        H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) (D.R.rS + 1) =
      H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) D.R.rS *
        H.Dl (fun a => sF Zd p a • baseChange₂ D p (f a)) (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) (D.R.rS + 1) := by
    have hr := hc.1
    rw [← FsLoc.gdl_eq, ← FsLoc.gdl_eq, ← FsLoc.gdl_eq, ← FsLoc.gdl_eq] at hr
    rw [dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ (Nat.le_succ _), dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ le_rfl,
      dl_loc Zd p f f₂ (sF Zd p) (sF' Zd p) _ (Nat.le_succ _), dl_loc Zd p f f₁ (sF Zd p) (sF' Zd p) _ le_rfl]
    have h := congrArg (D.s.atP p).ιE hr
    rw [map_mul, map_mul] at h
    linear_combination ((∏ i : Fin D.R.rS, (Zd.M p).L.cj (sF Zd p (Fin.castLE (Nat.le_succ _) i))) *
      (∏ i : Fin D.R.rS, sF' Zd p (Fin.castLE (Nat.le_succ _) i)) *
      ((∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sF Zd p (Fin.castLE le_rfl i))) *
      (∏ i : Fin (D.R.rS + 1), sF' Zd p (Fin.castLE le_rfl i)))) * h
  have hef : ∀ b, e (sF' Zd p b • baseChange₂ D p (f₁ b)) = sF' Zd p b • baseChange₂ D p (f₂ b) := fun b => by
    rw [map_smul, he, betaP_bc, hg1]
  have hz : e (sF' Zd p (Fin.last D.R.rS) • baseChange₂ D p (f₁ (Fin.last D.R.rS))) -
      sF' Zd p (Fin.last D.R.rS) • baseChange₂ D p (f₂ (Fin.last D.R.rS)) ∈ H.X (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) := by
    rw [hef, sub_self]; exact Submodule.zero_mem _
  obtain ⟨hI, hzS⟩ := FsLoc.ident_generic H (tLoc Zd p γ).abelian₂ ⊥ (fun a => sF Zd p a • baseChange₂ D p (f a))
    (fun b => sF' Zd p b • baseChange₂ D p (f₁ b)) (fun b => sF' Zd p b • baseChange₂ D p (f₂ b)) (tLoc Zd p γ).T (tLoc Zd p γ).T'
    e hisoL h12 h21 hX0 hX2 hW0 homp hom' hrat hz
  have hG := hgen p
  have hfr1 := hG.1.2.1
  have hfr2 := hG.1.2.2.1
  refine ⟨hG, ⟨hfr1.2.1, hfr1.2.2.1⟩, ⟨fun a b hab => ?_, ?_⟩, hI, ?_, hzS⟩
  · show H.h (sF' Zd p a • baseChange₂ D p (f₂ a)) (sF' Zd p b • baseChange₂ D p (f₂ b)) = 0
    rw [← hef, ← hef, hisoL]
    exact hfr2.2.1 a b hab
  · show H.h (sF' Zd p (Fin.last _) • baseChange₂ D p (f₂ (Fin.last _))) (sF' Zd p (Fin.last _) • baseChange₂ D p (f₂ (Fin.last _))) = _
    rw [← hef, hisoL]
    exact hfr2.2.2.1
  · intro x x₂ hx hx₂
    have : x = x₂ := Subtype.ext (hx.trans hx₂.symm)
    rw [this]
    rfl

variable (u u' F0 what₂)

set_option maxHeartbeats 1000000 in

theorem starExists2_of_parts (hP : CtxP u u' F0 what₂) (hGen : CohGen Zd u u' F0 what₂)
    (hIo : CohIota Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ := by
  intro γ Z hC
  obtain ⟨w, hγ, -⟩ := id hC
  obtain ⟨F'₂, hZ, hc, hU⟩ := starFrameU_holds γ Z hC
  obtain ⟨g, y, hiso, hg1, hform, hom⟩ := starGlob γ Z hC F'₂ hZ hU
  let φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂) :=
    fun p => FsLoc.starPhi Zd p g hiso (starFrame γ) (frame F'₂) hg1
  have hφ' : ∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂)
      (LinearEquiv.refl _ _) (φ' p) :=
    fun p => starIdentG Zd γ Z hC (starGenLoc_of_P Zd hP γ w hγ) F'₂ hZ hc hU g y hiso hg1 hform hom p
  have hH : CohHyp Zd γ Z F'₂ φ' := ⟨hC, hZ, hc, hφ'⟩
  have hlat : Submodule.IsLattice D.host.E γ.lam := (hP.2.1.1 γ.lam γ.mem).1.1
  have hLp : {p | ⇑(φ' p) '' (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (tLoc Zd p γ).f' ≠
      (locH Zd p).Lset (lattice₂ D Zd.M p γ.lam) (locF' Zd p F'₂)}.Finite := by
    refine ((FsLoc.localLattice_preserves_cofinite Zd g hlat).union (FsLoc.localLattice_preserves_cofinite_symm Zd g hlat)).subset ?_
    intro p hp
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
    exact hp (FsLoc.lset_map (locH Zd p) _ _ (betaP p g) (betaP_iso Zd p g hiso) _ _ _ hn.1 hn.2)
  have hResp : {p | ¬ (locH Zd p).Respects (tLoc Zd p γ) (CohCut.t2 Zd p γ F'₂ (lattice₂ D Zd.M p γ.lam))
      (LinearEquiv.refl _ _) (φ' p)}.Finite := by
    refine (hLp.union (hIo hP γ Z F'₂ φ' hH)).subset ?_
    intro p hp
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, ne_eq] at hn
    obtain ⟨h3, h5⟩ := hn
    apply hp
    refine ⟨?_, ?_, h3, (hH.2.2.2 p).2.2.2.2.2, h5⟩
    · exact Set.image_id _
    · intro x x₂ hx hx₂
      rw [one_smul, one_smul]
      show (locH Zd p).mkW _ x = (locH Zd p).mkW _ x₂
      exact congrArg _ (Subtype.ext (hx.trans hx₂.symm))
  refine ⟨F'₂, fun _ => LinearEquiv.refl _ _, φ', ⟨hZ, hφ', fun _ => rfl⟩, γ.lam, hlat, ?_⟩
  refine (((hGen hP γ Z F'₂ φ' hH).union hResp).union (hGood hP γ Z F'₂ φ' hH)).subset ?_
  intro p hp
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  obtain ⟨⟨hg, hr⟩, hN⟩ := hn
  exact hp (locSet_eq_single Zd ⟨hg, hr⟩ hN)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem starExists2_of_good (hP : CtxP u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_parts Zd u u' F0 what₂ hP (cohGen_of Zd (cohInt_holds Zd) (cohDG_holds Zd) hGood)
    (cohIota_holds Zd) hGood

theorem starExists2_holds (hP : CtxP u u' F0 what₂) : StarExists2 Zd u u' F0 what₂ :=
  starExists2_of_good Zd u u' F0 what₂ hP (cohGood_of Zd globGramNe_holds)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP OmL

namespace OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem mat_frameAct {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T')
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (frameAct (frame F') ξ b)) =
      Zhat F0 F'.fl * ξ.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  exact Matrix.ext fun a b => Formalism.L2.SG.Pf.AtPt.brS_frameAct (lf D F0) F' ξ a b

theorem map_det_eq {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V) :
    ((Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).map (D.s.atP p).ιE).det =
      (D.s.atP p).ιE (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det := (RingHom.map_det _ _).symm

theorem det_ne_of_unit {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (G : Fin (D.R.rS + 1) → (VS D).V)
    (h : IsUnit ((locH Zd p).Zhat (fL Zd p F0) (gL Zd p G)).det) :
    (Matrix.of fun a b => (VS D).hT (F0.fvec a) (G b)).det ≠ 0 := by
  intro h0
  rw [zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, h0, map_zero, mul_zero, zero_mul] at h
  exact not_isUnit_zero h

theorem gdl_eq {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') (l : ℕ) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl F0.fvec F'.fvec l = Formalism.MainNotions.S.Dl F0 F' l := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl Formalism.MainNotions.S.Dl leadMinorE
  split_ifs <;> rfl

end OmD

open OmD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

variable (u u' F0 what₂)

theorem modeMatrixDet_eq_adjointDet : OmDet Zd u u' F0 what₂ := by
  intro _ γ Z _ F'₂ φ φ' hS F' hP
  obtain ⟨p⟩ := Formalism.L2.SG.Pf.LocModel.plF_nonempty D
  have hT2 := hS.2.1 p
  have hunγ := hT2.1.1.2.2.2.1
  rw [dl_last] at hunγ
  have hdγ : (ZhatL (lf D F0) (repF γ)).det ≠ 0 := by
    have h1 := det_ne_of_unit Zd p F0
      (frameAct (frame (repF γ)) (admXi D γ.lam (lf D F0) (repF γ))⁻¹) hunγ
    rw [mat_frameAct, Matrix.det_mul] at h1
    exact left_ne_zero_of_mul h1
  refine ⟨hdγ, fun hZ => ?_⟩
  have hZ2 : (Matrix.of fun a b => (VS D).hT (F0.fvec a) (F'₂.fl.fvec b)) = Z := hS.1
  have hD2 : (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) = 0 := by
    rw [dl_last, zhat_fg, Matrix.det_mul, Matrix.det_mul, map_det_eq, hZ2, hZ, map_zero, mul_zero, zero_mul]
  have hId : (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' D.R.rS *
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) (D.R.rS + 1) =
      (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS *
        (locH Zd p).Dl (tLoc Zd p γ).f (tLoc Zd p γ).f' (D.R.rS + 1) := hT2.2.2.2.1.2.2.2.2.2
  rw [hD2, mul_zero] at hId
  obtain ⟨uγ, huγ⟩ := hT2.1.1.2.2.2.1
  rw [← huγ] at hId
  have hDr := (Units.mul_left_eq_zero uγ).1 hId.symm
  have e := Formalism.L2.SG.Pf.ScalarFramePf.dl_loc Zd p F0.fvec F'₂.fl.fvec (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p)
    (Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p) D.R.rS (Nat.le_succ _)
  rw [show (locH Zd p).Dl (fL Zd p F0) (gL Zd p F'₂.fl.fvec) D.R.rS = _ from e] at hDr
  have hu1 : IsUnit (∏ i : Fin D.R.rS, (Zd.M p).L.cj
      (Formalism.L2.SG.Pf.ScalarFramePf.sF Zd p (Fin.castLE (Nat.le_succ _) i))) :=
    IsUnit.prod_univ_iff.2 fun i => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map _
  have hu2 : IsUnit (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.ScalarFramePf.sF' Zd p (Fin.castLE (Nat.le_succ _) i)) :=
    IsUnit.prod_univ_iff.2 fun i => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _
  have hg := (hu1.mul hu2).mul_right_eq_zero.1 hDr
  rw [map_eq_zero_iff _ (D.s.atP p).ιE.injective, gdl_eq] at hg
  have hG := hP.1.1.2.2
  rw [fwdCut_gval_congr (lf D F0) F' F'₂ (hP.1.2.2.2.2.trans hS.1.symm)] at hG
  apply hG
  show Formalism.MainNotions.S.Gflag F0 F'₂.fl = 0
  unfold Formalism.MainNotions.S.Gflag
  rw [PI.UnitaryGroupMassFormula.BetaLUniq.GN.Dl_succ, hg, show Zhat F0 F'₂.fl = Z from hS.1, hZ]
  simp

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open scoped Classical
open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching Matrix

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

open OmP

namespace OmR

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth' {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S

theorem hswap (x y : S.V) : S.hT y x = star (S.hT x y) := NMoveP.hsw S x y

theorem orthX_of {T : E} (F : FlagG S r T) {v : S.V} (h : ∀ i, S.hT (F.e i) v = 0) : v ∈ orth S F.X :=
  mem_orth'.2 fun x hx => NMoveP.spanL S F.e v h x hx

theorem orthX_of_f {T : E} (F : FlagG S r T) {v : S.V} (h : ∀ a, S.hT (F.fvec a) v = 0) : v ∈ orth S F.X :=
  orthX_of F fun i => by rw [← fvec_cs]; exact h _

theorem om_orthX {T T' : E} {F : FlagG S r T} {F' : FlagG S r T'} {v : S.V} (h : OmV F F' v) :
    v ∈ orth S F.X :=
  orthX_of F fun i => by rw [← fvec_cs, h.2]; simp [Fin.castSucc_ne_last]

theorem z_orthX {T : E} (F : FlagG S r T) : F.z ∈ orth S F.X := orthX_of F F.z_orth

theorem X_le_sp {T : E} (F : FlagG S r T) : F.X ≤ Submodule.span E (Set.range F.fvec) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.castSucc, fvec_cs F i⟩

section NL

variable {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V}

theorem nl_isom (hn : n ∈ NLam Λ F) (x y : S.V) : S.hT (n x) (n y) = S.hT x y := hn.1.1 x y

theorem e_mem_flag (F : LFlag S r T) (i : Fin r) : F.fl.e i ∈ Xflag F (i.1 + 1) :=
  Submodule.subset_span ⟨i, show i.1 < i.1 + 1 from Nat.lt_succ_self _, rfl⟩

theorem flag_le_X (F : LFlag S r T) (j : ℕ) : Xflag F j ≤ Xsp F :=
  Submodule.span_mono (Set.image_subset_range _ _)

theorem nl_e (hn : n ∈ NLam Λ F) (i : Fin r) : n (F.fl.e i) - F.fl.e i ∈ Xsp F :=
  flag_le_X F i.1 (hn.2.1 i.1 _ (e_mem_flag F i))

theorem nl_X (hn : n ∈ NLam Λ F) {x : S.V} (hx : x ∈ Xsp F) : n x ∈ Xsp F := by
  have : Xsp F ≤ (Xsp F).comap (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range F.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show n (F.fl.e i) ∈ Xsp F
    have h := nl_e hn i
    have e : n (F.fl.e i) = (n (F.fl.e i) - F.fl.e i) + F.fl.e i := by abel
    rw [e]
    exact Submodule.add_mem _ h (Submodule.subset_span ⟨i, rfl⟩)
  exact this hx

theorem nl_orth (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ orth S (Xsp F)) : n v - v ∈ Xsp F := hn.2.2 v hv

theorem nl_symm_orth (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ orth S (Xsp F)) : n.symm v ∈ orth S (Xsp F) := by
  refine mem_orth'.2 fun x hx => ?_
  rw [← nl_isom hn x, LinearEquiv.apply_symm_apply]
  exact mem_orth'.1 hv _ (nl_X hn hx)

theorem sp_map_eq (hn : n ∈ NLam Λ F) :
    (Submodule.span E (Set.range F.fl.fvec)).map (n : S.V →ₗ[E] S.V) = Submodule.span E (Set.range F.fl.fvec) := by
  apply Submodule.eq_of_le_of_finrank_eq _ (LinearEquiv.finrank_map_eq n _)
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  have hX := X_le_sp F.fl
  have e : (n : S.V →ₗ[E] S.V) (F.fl.fvec b) = F.fl.fvec b + (n (F.fl.fvec b) - F.fl.fvec b) := by
    simp
  rw [e]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨b, rfl⟩) (hX ?_)
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [fvec_last]; exact nl_orth hn (z_orthX F.fl)
  · rw [fvec_cs]; exact nl_e hn i

end NL

section DC

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E} (F : LFlag S r T)

def Inv (Ωγ : S.V) (F₁ : LFlag S r T') : Prop := ∃ v, OmV F.fl F₁.fl v ∧ v - Ωγ ∈ Xsp F

def QU (F₁ : LFlag S r T') : Prop :=
  ∀ d ∈ Submodule.span E (Set.range F₁.fl.fvec), (∀ a, S.hT (F.fl.fvec a) d = 0) → d = 0

theorem qu_of_det (F₁ : LFlag S r T') (h : (Zhat F.fl F₁.fl).det ≠ 0) : QU F F₁ :=
  fun _ hd h0 => eq_zero_of_orth F.fl F₁.fl h hd h0

variable {F}

theorem sp_dc {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    (h : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    Submodule.span E (Set.range F₂.fl.fvec) = (Submodule.span E (Set.range F₁.fl.fvec)).map (n : S.V →ₗ[E] S.V) := by
  have e : F₂.fl.fvec = ((n : S.V →ₗ[E] S.V) ∘ₗ (m : S.V →ₗ[E] S.V)) ∘ F₁.fl.fvec := funext h
  rw [e, Set.range_comp, ← Submodule.map_span, Submodule.map_comp, sp_map_eq hm]

theorem inv_dc {Ωγ : S.V} {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : Inv F Ωγ F₁ ↔ Inv F Ωγ F₂ := by
  obtain ⟨n, hn, m, hm, hf, -⟩ := h
  have hsp := sp_dc hm hf
  constructor
  · rintro ⟨v, hv, hvγ⟩
    have hd := nl_orth hn (om_orthX hv)
    refine ⟨n v, ⟨?_, fun a => ?_⟩, ?_⟩
    · rw [hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]; exact hv.1
    · have e : n v = v + (n v - v) := by abel
      rw [e, map_add, NMoveP.hT_f_X F.fl a hd, add_zero, hv.2]
    · have e : n v - Ωγ = (n v - v) + (v - Ωγ) := by abel
      rw [e]; exact Submodule.add_mem _ hd hvγ
  · rintro ⟨v, hv, hvγ⟩
    have ho := nl_symm_orth hn (om_orthX hv)
    have hd := nl_orth hn ho
    rw [LinearEquiv.apply_symm_apply] at hd
    refine ⟨n.symm v, ⟨?_, fun a => ?_⟩, ?_⟩
    · have h1 := hv.1
      rw [hsp, Submodule.mem_map_equiv] at h1
      exact h1
    · have e : n.symm v = v - (v - n.symm v) := by abel
      rw [e, map_sub, NMoveP.hT_f_X F.fl a hd, sub_zero, hv.2]
    · have e : n.symm v - Ωγ = (v - Ωγ) - (v - n.symm v) := by abel
      rw [e]; exact Submodule.sub_mem _ hvγ hd

theorem qu_dc {F₁ F₂ : LFlag S r T'} (h : DCRel Λ F F₁ F₂) : QU F F₁ ↔ QU F F₂ := by
  obtain ⟨n, hn, m, hm, hf, -⟩ := h
  have hsp := sp_dc hm hf
  constructor
  · intro hq d hd h0
    have ho : d ∈ orth S (Xsp F) := orthX_of_f F.fl h0
    have ho' := nl_symm_orth hn ho
    have hdd := nl_orth hn ho'
    rw [LinearEquiv.apply_symm_apply] at hdd
    rw [hsp, Submodule.mem_map_equiv] at hd
    have : n.symm d = 0 := hq _ hd fun a => by
      have e : n.symm d = d - (d - n.symm d) := by abel
      rw [e, map_sub, NMoveP.hT_f_X F.fl a hdd, sub_zero, h0]
    simpa using congrArg n this
  · intro hq d hd h0
    have ho : d ∈ orth S (Xsp F) := orthX_of_f F.fl h0
    have hdd := nl_orth hn ho
    have hnd : n d ∈ Submodule.span E (Set.range F₂.fl.fvec) := by
      rw [hsp, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]; exact hd
    have : n d = 0 := hq _ hnd fun a => by
      have e : n d = d + (n d - d) := by abel
      rw [e, map_add, NMoveP.hT_f_X F.fl a hdd, add_zero, h0]
    simpa using this

theorem inv_eqv {P : LFlag S r T' → Prop} {x y : Carrier P} (h : Relation.EqvGen (Rel Λ F P) x y)
    (I : LFlag S r T' → Prop) (hI : ∀ F₁ F₂, DCRel Λ F F₁ F₂ → (I F₁ ↔ I F₂)) : I x.1 ↔ I y.1 := by
  induction h with
  | rel a b hab => exact hI _ _ hab
  | refl => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

end DC

section Pair

variable {Λ : Submodule (𝓞 E) S.V} {T T' : E}

theorem orth_orth (U : Submodule E S.V) : orth S (orth S U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro u hu
    refine mem_orth'.2 fun x hx => ?_
    rw [hswap, mem_orth'.1 hx u hu, star_zero]
  · have h1 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S U
    have h2 := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (orth S U)
    omega

theorem z_mem_UUE (F : LFlag S r T) (F' : LFlag S r T') (hF : IsLift Λ F) : F.fl.z ∈ UUE Λ F F' := by
  refine Submodule.subset_span ?_
  show F.fl.z ∈ (UU Λ F F' : Set S.V)
  rw [← hF.2]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
    (Submodule.mem_span_singleton_self _)))

theorem z'_mem_UUE (F : LFlag S r T) (F' : LFlag S r T') (hF' : IsLift Λ F') : F'.fl.z ∈ UUE Λ F F' := by
  refine Submodule.subset_span ?_
  show F'.fl.z ∈ (UU Λ F F' : Set S.V)
  rw [← hF'.2]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem sp_le_UUE (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hF' : IsLift Λ F') :
    Submodule.span E (Set.range F'.fl.fvec) ≤ UUE Λ F F' := by
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [fvec_last]; exact z'_mem_UUE F F' hF'
  · rw [fvec_cs]
    exact PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F' (Submodule.subset_span ⟨i, rfl⟩)

theorem pair_core (hΛ : Submodule.IsLattice E Λ) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (k : ℕ) (hLF : IsLift Λ F) (hL' : IsLift Λ F') (hL'' : IsLift Λ F'') (hG' : Gval F F' ≠ 0)
    (hdim : finrank E S.V = k + 2 * r + 1) (hT : T ≠ 0) (hs : s0 Λ F F' F'' β k = 1)
    (hsc : IsScalar Λ F F' F'' β) {Ω'' : S.V} (hΩ : OmV F.fl F''.fl Ω'') :
    ∃ w, OmV F.fl F'.fl w ∧ Ω'' - w ∈ Xsp F := by
  have n' := PI.UnitaryGroupMassFormula.BetaLUniq.gram_matrix_nondegenerate S Λ F F' hΛ hLF hL' hG'
  have hHp : finrank E (Hp Λ F F') + (2 * r + 2) = finrank E S.V := by
    have := PI.UnitaryGroupMassFormula.BetaLUniq.finrank_orth_add S (UUE Λ F F')
    rw [n'.1] at this
    exact this
  have hle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod] at hp
    exact hp.1.1.1
  have hTh : Th Λ F F' F'' β = Hp Λ F F' := by
    apply Submodule.eq_of_le_of_finrank_le hle
    simp only [s0] at hs
    omega
  set ν : S.V := Ω'' + T⁻¹ • F.fl.z with hν
  have hzX : F.fl.z ∈ orth S (Xsp F) := z_orthX F.fl
  clear_value ν
  have hνX : ν ∈ orth S (Xsp F) := by
    rw [hν]; exact Submodule.add_mem _ (om_orthX hΩ) (Submodule.smul_mem _ _ hzX)
  have hνU'' : ν ∈ UUE Λ F F'' := by
    rw [hν]; exact Submodule.add_mem _ (sp_le_UUE hΛ F F'' hL'' hΩ.1) (Submodule.smul_mem _ _ (z_mem_UUE F F'' hLF))
  have hνH : ν ∈ orth S (Hp Λ F F') := by
    refine mem_orth'.2 fun x hx => ?_
    rw [← hTh] at hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    simp only [ThPairs, Submodule.mem_inf, Submodule.mem_prod, Submodule.mem_comap, LinearMap.sub_apply,
      LinearMap.fst_apply, LinearMap.snd_apply] at hp
    have e : p.1 = p.2 + (p.1 - p.2) := by abel
    simp only [LinearMap.fst_apply]
    rw [e, LinearMap.map_add₂, mem_orth'.1 hνX _ hp.1.2]
    have h2 : S.hT ν p.2 = 0 := mem_orth'.1 hp.1.1.2 ν hνU''
    rw [hswap, h2, star_zero, add_zero]
  have hνU' : ν ∈ UUE Λ F F' := by
    have := hνH
    rw [show Hp Λ F F' = orth S (UUE Λ F F') from rfl, orth_orth] at this
    exact this
  have hzz : S.hT F.fl.z ν = 0 := by
    have h1 : S.hT F.fl.z Ω'' = 1 := by rw [← fvec_last, hΩ.2]; simp
    rw [hν, map_add, map_smul, h1, F.fl.z_norm, smul_eq_mul]
    field_simp
    ring
  have hνXp : ν ∈ orth S (Xplus F) := by
    refine mem_orth'.2 fun x hx => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    rw [LinearMap.map_add₂, mem_orth'.1 hνX a ha, NMoveP.hT_smulL, hzz, mul_zero, add_zero]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hΩ.1
  have hSg'' : SgRel F F'' ν 0 T⁻¹ (c (Fin.last r)) := by
    refine ⟨0, Submodule.zero_mem _, ∑ i : Fin r, c i.castSucc • F''.fl.e i,
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
    rw [hLF.2, hL''.2, hν, ← hc, Fin.sum_univ_castSucc, fvec_last]
    simp only [fvec_cs, sub_zero, add_zero]
    abel
  have hY : ∀ {F₁ : LFlag S r T'}, ν ∈ UUE Λ F F₁ → ν ∈ Ylift Λ F F₁ := fun h => Submodule.mem_inf.2 ⟨h, hνXp⟩
  obtain ⟨x, hx, x', hx', hE⟩ := (hsc ν (hY hνU') ν (hY hνU'') 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)
    (by simp) (by simp) T⁻¹ (c (Fin.last r))).2 hSg''
  refine ⟨Ω'' - x, ⟨?_, fun a => ?_⟩, by simpa using hx⟩
  · have e : Ω'' - x = c (Fin.last r) • F'.fl.z + x' := by
      rw [hLF.2, hL'.2, sub_zero, hν] at hE
      have := congrArg (fun v => v - T⁻¹ • F.fl.z - x) hE
      rw [show Ω'' - x = Ω'' + T⁻¹ • F.fl.z - T⁻¹ • F.fl.z - x by abel, this]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.last r, fvec_last _⟩))
      (X_le_sp F'.fl hx')
  · rw [map_sub, NMoveP.hT_f_X F.fl a hx, sub_zero, hΩ.2]

end Pair

end OmR

open OmR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem omRep_repF (γ : TermDef.Term D u u' F0 what₂) :
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls (repF γ) := by
  unfold repF
  split
  · rename_i x hx
    unfold nrep at hx
    split_ifs at hx with h
    cases hx
    exact h.choose_spec.1
  · exact ⟨(Quot.out γ.cls).2, Quot.out_eq _⟩

variable (u u' F0 what₂)

theorem omega_representative_holds : OmRep u u' F0 what₂ := by
  intro hrows γ Z _ hdγ _ F' hP Ω' Ωγ h' hγ
  obtain ⟨-, γ', ⟨p, hp1, hp2, hpS⟩, hrep⟩ := hP
  have hrepγ := omRep_repF γ
  obtain ⟨lam, mem, cls⟩ := γ
  obtain ⟨lam', mem', cls'⟩ := γ'
  simp only [Corank.Pair.pfst] at hp1
  simp only [Corank.Pair.psnd] at hp2
  cases hp1
  cases hp2
  obtain ⟨hPγ, eγ⟩ := hrepγ
  obtain ⟨hP', e'⟩ := hrep
  have r1 := Quot.eqvGen_exact eγ
  have r2 := Quot.eqvGen_exact e'
  have hRL := hrows.1 p.lam p.mem
  have hΛ : Submodule.IsLattice D.host.E p.lam := hRL.2.1.1
  have hLF : IsLift p.lam (lf D F0) := hRL.2.1.2.2.1

  have i1 := (inv_eqv r1 (Inv (lf D F0) Ωγ) fun _ _ h => inv_dc h).1 ⟨Ωγ, hγ, by simp⟩
  have q1 := (inv_eqv r1 (QU (lf D F0)) fun _ _ h => qu_dc h).1 (qu_of_det _ _ hdγ)

  have i2 := (inv_eqv r2 (Inv (lf D F0) Ω') fun _ _ h => inv_dc h).1 ⟨Ω', h', by simp⟩
  obtain ⟨v', hv', hv'γ⟩ := i1
  obtain ⟨v'', hv'', hv''Ω⟩ := i2
  obtain ⟨w, hw, hw''⟩ := pair_core hΛ (lf D F0) p.fst.1 p.snd.1 p.beta D.R.k hLF p.fst.2.1 p.snd.2.1 p.G_fst
    (Corank.finrank_VS D) (Corank.tu_ne_zero u) hpS.1 hpS.2 hv''
  have e : v' = w := sub_eq_zero.1 (q1 _ (Submodule.sub_mem _ hv'.1 hw.1) fun a => by
    rw [map_sub, hv'.2, hw.2, sub_self])
  subst e
  have : Ω' - Ωγ = (v' - Ωγ) + (v'' - v') - (v'' - Ω') := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.add_mem _ hv'γ hw'') hv''Ω

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem omega_part_holds : OmPart Zd u u' F0 what₂ :=
  omPart_of Zd (modeMatrixDet_eq_adjointDet Zd u u' F0 what₂) (omega_local_holds Zd u u' F0 what₂) (omega_representative_holds u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} {Zd : LocDat D} {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
  {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}

theorem bwdTerm'_of_gx (hGX : GenXiRev Zd u' F0) : BwdTerm' Zd u u' F0 what₂ :=
  bwdTerm'_of' (btOK_holds Zd) hGX

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V))

theorem bwdTerm'_holds : BwdTerm' Zd u u' F0 what₂ := bwdTerm'_of_gx (genXiRev_holds Zd)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem bwdBeta'_of_leaves (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) :
    BwdBeta' Zd u u' F0 what₂ :=
  bwdBeta'_of_core Zd repG_holds (betaCore_of₂ Zd (betaCore₂_of Zd hRat (scalarOf_holds Zd) hInt))

theorem fStarC_of_leaves' (hC : CtxP u u' F0 what₂) (hLP : LprPart Zd u u' F0 what₂)
    (hRat : BetaRat Zd u u' F0 what₂) (hInt : BetaInt Zd u u' F0 what₂) : FStarC Zd u u' F0 what₂ :=
  fStarC_of_route2 Zd (starExists2_holds Zd u u' F0 what₂ hC)
    (fwdC_of_loc Zd hC.2.1 (omega_part_holds Zd u u' F0 what₂) (genXi_holds Zd) hLP)
    (bwdC_of''' Zd hC (bwdN_holds Zd u u' F0 what₂) (bwdTerm'_holds Zd u u' F0 what₂) (bwdBeta'_of_leaves Zd hRat hInt))
    (Uniq.uniqC_holds Zd u u' F0 what₂)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
end
end
