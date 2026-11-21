import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalizedLatticeEqOfAdelicMatricesAgreeAtPlace
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import BuildAid.ForwardExisting
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatSLatAdIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainChartFramesBadPrimeCongruentOneOfAdelicAgre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruentOneMemStepLevelLevelCharEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCharDetEqOneOfCongrOneModPow

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
  first | exact @GlobalTheory.LatAway.decoAt_eq | exact GlobalTheory.LatAway.decoAt_eq | (intros; apply GlobalTheory.LatAway.decoAt_eq <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.AwayLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem prV_pullV_mem_latS_dual : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  have hmono : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) lev.Lb ≤
      latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) :=
    Submodule.span_mono (Set.image_mono fun y hy => Submodule.subset_span (lev.Lb_int y hy))
  apply hmono
  induction hl using Submodule.span_induction with
  | mem y hy => exact Formalism.L2.Geo.Def.PN.prV_latS lev.Lb v hy
  | zero =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) k)) = 0 := by
      ext k
      have h0 : pullV (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) = 0 := by
        have := pullV_add (F := D.host.F) x.1 (0 : Fin (D.R.N i) → D.host.E) 0
        funext j
        have hj := this j
        rw [add_zero] at hj
        simpa using hj
      rw [h0, Pi.zero_apply, map_zero, Pi.zero_apply]
    rw [this]; exact zero_mem _
  | add a b _ _ ha hb =>
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (a + b) k)) =
        (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) +
          (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 b k)) := by
      ext k
      rw [Pi.add_apply, pullV_add, map_add]
    rw [this]; exact add_mem ha hb
  | smul c a _ ha =>
    have hc : inclE (F := D.host.F) (v.adicCompletion D.host.F) (algebraMap (𝓞 D.host.E) D.host.E c) ∈ intV D.host.E v :=
      Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 D.host.E) D.host.E c, ⟨c, rfl⟩⟩, rfl⟩)
    have : (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 (c • a) k)) =
        (⟨_, hc⟩ : intV D.host.E v) • (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 a k)) := by
      ext k
      rw [pullV_osmul, map_mul]
      rfl
    rw [this]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.AwayLat
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ latAd x.1 lev.Lb →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  atlas_forward_decl GlobalTheory.AwayLat.prV_pullV_mem_latS_dual
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

namespace GlobalTheory.ZDual

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem pullV_dual_mem_latS_gen (σ : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    (v : HeightOneSpectrum (𝓞 F)) (l : Fin N → E) (hl : l ∈ dualSet (σ : E →+* E) J (latAd x Lb)) :
    (fun k => prV (E := E) v (pullV (F := F) x l k)) ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J Lb)) := by
  have hU : cT (sigR σ (v.adicCompletion F)) (bc (prV (E := E) v) x).val *
      J.map (inclE (F := F) (v.adicCompletion F)) * (bc (prV (E := E) v) x).val =
      J.map (inclE (F := F) (v.adicCompletion F)) := Formalism.UG.P.afsplit_bc_mem σ J v x hx
  have hy : (fun k => prV (E := E) v (pullV (F := F) x l k)) =
      ((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)) := by
    rw [GlobalTheory.LocCarry.coe_bc_inv]
    funext k
    unfold pullV
    rw [RingHom.map_mulVec]
    rfl
  rw [hy]
  refine GlobalTheory.St.G.Dual.bwd_loc σ J hJ.ne_zero Lb ⟨hfin, hspan⟩ v _ fun b hb => ?_
  unfold GlobalTheory.St.G.hR
  have key := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (bc (prV (E := E) v) x).val (fun k => inclE (F := F) (v.adicCompletion F) (b k))
    (((bc (prV (E := E) v) x)⁻¹).val *ᵥ (fun k => inclE (F := F) (v.adicCompletion F) (l k)))
  rw [hU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at key
  rw [← key]
  refine Formalism.L2.G.RelativeIndexFlags.pair_int v σ J (latAd x Lb) l hl _ ?_
  rw [GlobalTheory.LocCarry.mem_latS_latAd_iff x Lb hfin hspan v, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨b, hb, rfl⟩

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem pullV_dual_mem_latS : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  intro D i hi T f bad lev x v l hl
  exact pullV_dual_mem_latS_gen (sigD D) (gramN D i hi) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D i hi) lev.Lb lev.Lb_fin
    lev.Lb_span x.1 x.2 v l hl

end GlobalTheory.ZDual
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice : ∀ {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (l : Fin (D.R.N i) → D.host.E), l ∈ dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (latAd x.1 lev.Lb) →
    (fun k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)) := by
  atlas_forward_decl GlobalTheory.ZDual.pullV_dual_mem_latS
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

namespace GlobalTheory.FnlAway

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem T_mem_under {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (P : t.Pr.vT (t.word u))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : IsOver v (seamP t.seam P.1)) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h1 : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    have := Ideal.absNorm_mem P.1.asIdeal
    rwa [t.pr_ok.vT_norm _ P.1 P.2] at this
  rw [t.T_rec] at h1
  have h2 := (mem_seamP t.seam P.1 _).2 h1
  rw [map_natCast] at h2
  unfold IsOver at hv
  rw [hv, Ideal.mem_comap, map_natCast]
  exact h2

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (g g₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (w : Fin n → E) (l : Fin n) :
    prV (E := E) v (pullV (F := F) g₁ w l) = prV (E := E) v (pullV (F := F) g w l) := by
  have key : ∀ k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) k w l) =
      ∑ j, ((bc (prV (E := E) v) k)⁻¹ : GL (Fin n) _).1 l j * prV (E := E) v (Formalism.L2.Col.iA F E (w j)) := by
    intro k
    rw [← map_inv]
    unfold pullV
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  rw [key, key, h]

set_option maxHeartbeats 6000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem exists_unit_one_add_generator {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad)
    (crd : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Fin (D.R.N i) → D.host.E) (hw : w ∈ latCo D.sp (gramN D i hi) crd a x.1 lev.Lb) :
    ∃ z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)),
      z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F crd * x.1) w l) := by
  let M := latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb))
  have hint : ∀ c : 𝓞 D.host.E, inclE (F := D.host.F) (v.adicCompletion D.host.F) (c : D.host.E) ∈ intV D.host.E v :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)
  let φ : (Fin (D.R.N i) → D.host.E) → (Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
    fun l k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)
  have hadd : ∀ l₁ l₂, φ (l₁ + l₂) = φ l₁ + φ l₂ := by
    intro l₁ l₂
    funext k
    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  have hzero : φ 0 = 0 := by
    funext k
    simp [φ, pullV, Matrix.mulVec, dotProduct]
  have hsmul : ∀ (c : 𝓞 D.host.E) l, φ (c • l) = (⟨_, hint c⟩ : intV D.host.E v) • φ l := by
    intro c l
    funext k
    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show c • l j = (c : D.host.E) * l j from Algebra.smul_def c (l j), map_mul, map_mul, map_mul, map_mul, mul_left_comm]
    congr 1
  have hmem : ∀ l ∈ compan (sp := D.sp) (gramN D i hi) a (latAd x.1 lev.Lb), φ l ∈ M := by
    intro l hl
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := Submodule.mem_sup.1 hl
    rw [hadd]
    refine M.add_mem (GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span i hi lev x v l₁ h₁) ?_
    refine Submodule.smul_induction_on h₂ ?_ ?_
    · intro r hr s hs
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [hsmul]
      refine M.smul_mem _ ?_
      induction hs using Submodule.span_induction with
      | mem s hs => exact GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice i hi lev x v s hs
      | zero => rw [hzero]; exact M.zero_mem
      | add p q _ _ hp hq => rw [hadd]; exact M.add_mem hp hq
      | smul c s _ h => rw [hsmul]; exact M.smul_mem _ h
    · intro p q hp hq
      rw [hadd]
      exact M.add_mem hp hq
  unfold latCo at hw
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hw
  refine ⟨⟨_, hmem l hl⟩, funext fun k => congrArg (prV (E := D.host.E) v) (congrFun ?_ k)⟩
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  symm
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, toLE_apply, ← map_inv]
  show ((((crd⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) *ᵥ _) j = _
  refine (RingHom.map_mulVec _ _ _ j).symm.trans ?_
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in

theorem fnl_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree y hy
  have hat := GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree
  set v := HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1) with hvdef
  have hvo : IsOver v (seamP t.seam P.1) := by
    unfold IsOver
    rw [hvdef, HeightOneSpectrum.under_asIdeal]
  have hTv : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    rw [htie.T_eq]
    exact T_mem_under t u P v hvo
  have hd := p.deco.2
  have hd₁ := p₁.deco.2
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 _ y).1 hy
  have hy₁ : y ∈ p₁.deco.1.at P.1 := hat ▸ hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 _ y).1 hy₁
  have hsP : s * s₁ ∉ P.1.asIdeal := fun h => (P.1.isPrime.mem_or_mem h).elim hs hs₁
  have hw : (s * s₁) • y ∈ p.deco.1.N := by
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ hsy
  have hw₁ : (s * s₁) • y ∈ p₁.deco.1.N := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hsy₁
  have hlat : (fun l => t.seam.iE (((s * s₁) • y) l)) ∈
      latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨_, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator i hi ((St i hi).K β).lev (A.crd i hi) a x v _ hlat
  have e1 := hp.fnl P v hTv hvo _ hw z hz
  have hz₁ : z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd i hi) * x₁.1)
      (fun b => t.seam.iE (((s * s₁) • y) b)) l) := by
    have hbc : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1) :=
      ((MonoidHom.map_mul _ _ _).trans (congrArg (bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi)) * ·) (hagree v hvo))).trans
        (MonoidHom.map_mul _ _ _).symm
    refine hz.trans (funext fun l => ?_)
    exact (prV_pullV_congr (F := D.host.F) (E := D.host.E) v (ratA D.host.F (A.crd i hi) * x.1)
      (ratA D.host.F (A.crd i hi) * x₁.1) hbc (fun b => t.seam.iE (((s * s₁) • y) b)) l).symm
  have e2 := hp₁.fnl P v hTv hvo _ hw₁ z hz₁
  have f1 := hd.f_smul P (s * s₁) y hy
  have f2 := hd₁.f_smul P (s * s₁) y hy₁
  haveI := P.1.isPrime
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hne
  rw [← f1, ← f2, e1, e2]

end GlobalTheory.FnlAway
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  atlas_forward_decl GlobalTheory.FnlAway.fnl_eq
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := by
  first | exact @GlobalTheory.FrameAway.frame_away | exact GlobalTheory.FrameAway.frame_away | (intros; apply GlobalTheory.FrameAway.frame_away <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := by
  first | exact @GlobalTheory.LevOne.cong_mem_level_chr_one | exact GlobalTheory.LevOne.cong_mem_level_chr_one | (intros; apply GlobalTheory.LevOne.cong_mem_level_chr_one <;> assumption)
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localChar_det_eq_one_of_congr_one_mod_pow : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := by
  first | exact @GlobalTheory.AwayMat.muAt_det_congr_one | exact GlobalTheory.AwayMat.muAt_det_congr_one | (intros; apply GlobalTheory.AwayMat.muAt_det_congr_one <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

noncomputable section

namespace GlobalTheory.AwayMat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levOne_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (j : ℕ), j ≤ m2 → ∀ (b : L.β j) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N j)) l))) →
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (k x)) ∧ chiInv Ch sel mu cst j P (L.h j b P) r = 1 := GlobalTheory.T.congruentOne_mem_stepLevel_levelChar_eq_one

theorem muAt_det_of_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ) (P : rowSG Pr sel mu) (n : ℕ) (k : Sp X.E n ≃ₗ[X.E] Sp X.E n),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E n) l))) →
    muAt Ch sel mu cst i P ((LinearEquiv.det k : X.Eˣ) : X.E) = 1 := GlobalTheory.T.localChar_det_eq_one_of_congr_one_mod_pow

theorem xiAt_cong : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ),
    X.AbelianUnramifiedExtensionConditions → Pr.Ok → Ch.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (i : ℕ), i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (P : rowSG Pr sel mu)
    (k : Sp X.E (R.N i) ≃ₗ[X.E] Sp X.E (R.N i)) (k' : Sp X.E (R.N (i + 1)) ≃ₗ[X.E] Sp X.E (R.N (i + 1))),
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N i)) l))) →
    (∀ s l, IntAt P.1 (((qOf P.1 : X.E) ^ cst.D P)⁻¹ * (k' (Pi.single s (1 : X.E)) l - (Pi.single s (1 : X.E) : Sp X.E (R.N (i + 1))) l))) →
    ∀ x, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr k k' x) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hCh hsel hL i hi al be P k k' hk hk' x
  obtain ⟨r, hr, hrk, hc⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi.le al P k hk
  obtain ⟨r', hr', hrk', hc'⟩ := levOne_of_cong Ch sel mu cst L G m2 hX hPr hCh hsel hL (i + 1) hi be P k' hk'
  have h := GlobalTheory.UnfoldTwoSided.xiAt_two_sided Ch sel mu cst L G m2 hX hPr hCh hsel hL i hi al be P r r' k k' hr hr' hrk hrk' x
  rw [hc, hc', muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k hk, muAt_det_of_cong Ch sel mu cst L G m2 hX hPr hsel hL i P _ k' hk'] at h
  simpa only [one_mul] using h

theorem decoAtT_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    p₁.deco.1.at P.1 = p.deco.1.at P.1 ∧ ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := fun A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv => ⟨GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv, GlobalTheory.T.chartFunctional_eq_of_agree_under_levelPrime A dtU a H T i hi β x x₁ p p₁ h1 h2 P hv⟩

theorem frames_cong : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : SB t μ,
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∃ k : Sp t.X.E (D.R.N i) ≃ₗ[t.X.E] Sp t.X.E (D.R.N i), frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * k ∧
      ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N i)) l)) := GlobalTheory.T.chainChart_frames_badPrime_congruent_one_of_adelic_agree

theorem inFr_mul {E : Type} [Field E] {n n' : ℕ} (f k : Sp E n ≃ₗ[E] Sp E n) (f' k' : Sp E n' ≃ₗ[E] Sp E n') (z : HomE E n n') :
    inFr (f * k) (f' * k') z = inFr k k' (inFr f f' z) := LinearMap.ext fun _ => rfl

theorem ptAway_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i < t.m2 → PtAway A a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi him
  intro β β' x x' x₁ x₁' p p' p₁ p₁' h1 h2 h3 h4 hag
  classical
  have hSS : (t.rd u μ).SS = Sall t.sel (t.tup μ) (t.word u) := ((isChainTop_iff _ _ _ _ _ _ _ _ _).1 T.isChainTop).1
  have hv : ∀ Q, Q ∈ Sall t.sel (t.tup μ) (t.word u) → ∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam Q) →
      bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1 ∧ bc (prV (E := D.host.E) v) x₁'.1 = bc (prV (E := D.host.E) v) x'.1 :=
    fun Q hQ v hvQ => hag v ⟨seamP t.seam Q, (mem_ssRec t u μ Q).2 (hSS ▸ hQ), hvQ⟩
  have hX : t.X.AbelianUnramifiedExtensionConditions := H.fields
  have hCh : t.Ch.Ok := H.ch.ch_ok
  have hL := t.idx_ok μ
  funext z
  unfold xiPt
  rw [dif_pos him, dif_pos him]
  unfold XiEntry
  refine congrArg₂ (· * ·) ?_ ?_
  · have eA := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').1)
    have eA' := fun P : t.Pr.vT (t.word u) => decoAtT_eq A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_left _ P.2) v hv').2)
    have key : (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p₁.deco.1.at P.1, z y ∈ p₁'.deco.1.at P.1 ∧ p₁'.deco.1.f P (z y) = p₁.deco.1.f P y) ↔
        (∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y) := by
      refine forall_congr' fun P => ?_
      obtain ⟨a1, f1⟩ := eA P
      obtain ⟨a2, f2⟩ := eA' P
      rw [a1, a2]
      refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
      rw [f1 y hy, f2 _ hzy]
    unfold phiT
    by_cases hc : ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, z y ∈ p'.deco.1.at P.1 ∧ p'.deco.1.f P (z y) = p.deco.1.f P y
    · rw [if_pos hc, if_pos (key.2 hc)]
    · rw [if_neg hc, if_neg (fun h => hc (key.1 h))]
  · refine Finset.prod_congr rfl fun P _ => ?_
    obtain ⟨k, hk, hkc⟩ := frames_cong A dtU a H T i _ β x x₁ p p₁ h1 h3 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').1)
    obtain ⟨k', hk', hkc'⟩ := frames_cong A dtU a H T (i + 1) hi β' x' x₁' p' p₁' h2 h4 P
      (fun v hv' => (hv P.1 (Finset.mem_union_right _ P.2) v hv').2)
    rw [hk, hk', inFr_mul]
    exact xiAt_cong t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.glob t.m2 hX t.pr_ok hCh H.sel hL i him _ _ P k k' hkc hkc' _

end GlobalTheory.AwayMat
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_matrixStep : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i hi, i < t.m2 → PtAway A a i hi) := by
  atlas_forward_decl GlobalTheory.AwayMat.ptAway_mat
end
