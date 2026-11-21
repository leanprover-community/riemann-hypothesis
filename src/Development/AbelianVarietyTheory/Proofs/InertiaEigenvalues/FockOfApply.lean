import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot

section
noncomputable section

namespace GlobalTheory.ChoiceRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Choice

variable {D : D7}

abbrev Tgt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Type :=
  FractionRing (c.Oe w) ⊗[D.ntw.Ok (c.twI w) (c.k' w)]
    D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))

def BasisAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) : Prop :=
  ∀ b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j))
      D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j),
    LinearIndependent (FractionRing (c.Oe w)) (fun i => e (b i)) ∧
      Submodule.span (FractionRing (c.Oe w)) (Set.range fun i => e (b i)) = ⊤

def latT (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ) : Submodule (c.Oe w) (Tgt c w j) :=
  Submodule.span (c.Oe w)
      ((TensorProduct.mk (D.ntw.Ok (c.twI w) (c.k' w)) (FractionRing (c.Oe w))
          (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w)))) 1) ''
        (D.nexp.MtLat (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))) :
          Set (D.nexp.MtV (c.twI w) j (c.sd w) (c.k' w) (c.Q w) ((c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))))))

def latS (w : D.what₂.places.Pl) (j : ℕ) : Set (D.what₂.MtL (D.what₂.muTw w) j) :=
  {x | D.what₂.jMt (D.what₂.muTw w) j x ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen}

def LatAt (c : NChoice D) (w : D.what₂.places.Pl) (j : ℕ)
    (e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) (t : FractionRing (c.Oe w)) : Prop :=
  Submodule.span (c.Oe w) (e '' latS w j) = Submodule.span (c.Oe w) ((fun y => t • y) '' (latT c w j : Set (Tgt c w j)))

theorem BasisAt.smul {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (h : BasisAt c w j e) (u : (FractionRing (c.Oe w))ˣ) :
    BasisAt c w j ((u : FractionRing (c.Oe w)) • e) := by
  intro b
  obtain ⟨h1, h2⟩ := h b
  refine ⟨?_, ?_⟩
  · convert h1.units_smul (fun _ => u) using 1
    funext i
    simp [LinearMap.smul_apply, Units.smul_def]
  · have h3 : (Set.range fun i => ((u : FractionRing (c.Oe w)) • e) (b i)) =
        (u : FractionRing (c.Oe w)) • Set.range fun i => e (b i) := by
      rw [← Set.range_smul]; rfl
    rw [h3, Submodule.span_smul_eq_of_isUnit _ _ u.isUnit, h2]

theorem LatAt.smul_inv {c : NChoice D} {w : D.what₂.places.Pl} {j : ℕ}
    {e : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j} (u : (FractionRing (c.Oe w))ˣ)
    (h : LatAt c w j e (u : FractionRing (c.Oe w))) :
    Submodule.span (c.Oe w) ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = latT c w j := by
  let f : Tgt c w j →ₗ[c.Oe w] Tgt c w j :=
    { toFun := fun y => ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • y
      map_add' := fun _ _ => smul_add _ _ _
      map_smul' := fun r y => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (FractionRing (c.Oe w)) r y, ← algebraMap_smul (FractionRing (c.Oe w)) r,
          smul_smul, smul_smul, mul_comm] }
  have h1 : ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • e) '' latS w j) = f '' (e '' latS w j) := by
    rw [Set.image_image]; rfl
  rw [h1, Submodule.span_image, h, ← Submodule.span_image, Set.image_image]
  have h2 : (fun y => f ((u : FractionRing (c.Oe w)) • y)) = id := by
    funext y
    show ((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w)) • ((u : FractionRing (c.Oe w)) • y) = y
    rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  rw [h2, Set.image_id, Submodule.span_eq]

def withE (c : NChoice D) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : NChoice D :=
  { c with
    eMt := E
    eMt_basis := fun w j hw h1 h2 b => hb w j hw h1 h2 b
    eMt_lat := fun w j hw h1 h2 => hl w j hw h1 h2 }

def tupWithE {cf : CharFrame D} {c : NChoice D} (tp : TupTied D cf c) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) : TupTied D cf (withE c E hb hl) :=
  { tp with }

theorem choiceSide_withE {cf : CharFrame D} {mt : MtFam D} {exp : NExpTied D} {c : NChoice D} {tp : TupTied D cf c}
    (h : GlobalTheory.HeightCounting.ChoiceSide D cf mt exp c tp) (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j) :
    GlobalTheory.HeightCounting.ChoiceSide D cf mt exp (withE c E hb hl) (tupWithE tp E hb hl) :=
  ⟨⟨h.nct.twOf_eq, h.nct.twSide_eq, h.nct.Q_eq, h.nct.psi_eq, h.nct.embedding_baseField_condition⟩,
    ⟨h.choice.twI_conj, h.choice.sd_place, h.choice.emb_side, h.choice.sd_conj, h.choice.one, h.choice.conj⟩,
    h.off, h.adm, h.psi, h.eMt_level⟩

open Classical in

def pick (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) :
    ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j
  | w, 0 => c.eMt w 0
  | w, k + 1 => if h : D.what₂.muAt w ≠ D.what₂.mu0 ∧ k < D.R.m then G w h.1 ⟨k, h.2⟩ else c.eMt w (k + 1)

theorem pick_eq (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (w : D.what₂.places.Pl) (hw : D.what₂.muAt w ≠ D.what₂.mu0) (i : Fin D.R.m) : pick c G w (i.1 + 1) = G w hw i := by
  simp only [pick, dif_pos (And.intro hw i.2)]

theorem pick_prop (c : NChoice D)
    (G : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → ∀ i : Fin D.R.m,
      D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1))
    (p : ∀ w j, (D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j) → Prop)
    (h : ∀ w hw (i : Fin D.R.m), p w (i.1 + 1) (G w hw i)) :
    ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → p w j (pick c G w j) := by
  intro w j hw h1 h2
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have := h w hw ⟨k, by omega⟩
  rwa [← pick_eq c G w hw ⟨k, by omega⟩] at this

end Choice

section Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {S : RatDat D.ntw}

def ThetaAt (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (YS : NExpRealS R cG S) (c : NChoice D) (w : D.what₂.places.Pl)
    (i : Fin D.R.m) (e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)) (t : FractionRing (c.Oe w)) :
    Prop :=
  ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (i.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK S (i.1 + 1)),
    (R.FW i).j (sg0 D A3.A) ((YS.fi i).e (∑ k, a k • (show ↥(S.A (i.1 + 1)).WK from f k).1)) =
      Y.mj.eW i (D.what₂.thetaP (D.what₂.muTw w) (i.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (i.1 + 1) x)) →
    NChoice.thPe D c w (i.1 + 1) (e x) =
      t • ∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
        (YS.eF (c.twI w) (i.1 + 1) (c.sd w) (by omega) (by omega)).symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)

theorem ThetaAt.smul_inv {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    {w : D.what₂.places.Pl} {i : Fin D.R.m} {e : D.what₂.MtL (D.what₂.muTw w) (i.1 + 1) →ₛₗ[c.embW w] Tgt c w (i.1 + 1)}
    (u : (FractionRing (c.Oe w))ˣ) (h : ThetaAt Y YS c w i e (u : FractionRing (c.Oe w))) :
    ThetaAt Y YS c w i ((((u⁻¹ : (FractionRing (c.Oe w))ˣ) : FractionRing (c.Oe w))) • e) 1 := by
  intro x hx n a f hf
  rw [one_smul, LinearMap.smul_apply, map_smul, h x hx n a f hf, smul_smul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

theorem emtTheta_withE {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {YS : NExpRealS R cG S} {c : NChoice D}
    (E : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[c.embW w] Tgt c w j)
    (hb : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → BasisAt c w j (E w j))
    (hl : ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m →
      Submodule.span (c.Oe w) (E w j '' latS w j) = latT c w j)
    (h : ∀ w (i : Fin D.R.m), D.what₂.muAt w ≠ D.what₂.mu0 → ThetaAt Y YS c w i (E w (i.1 + 1)) 1) :
    GlobalTheory.HeightCounting.EMtTheta Y YS (withE c E hb hl) := by
  intro w i hw x hx n a f hf
  have := h w i hw x hx n a f hf
  rw [one_smul] at this
  exact this

end Rows

end GlobalTheory.ChoiceRead

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead

variable {D : D7}

abbrev Amb (D : D7) (j : Fin D.R.m) : Type := Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank

section Choice

variable (c : NChoice D) (w : D.what₂.places.Pl)

abbrev KE : Type := FractionRing (c.Oe w)

abbrev chr : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ := (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {c w}

def viaOk (ι : KE c w →+* ℂ) : D.ntw.Ok (c.twI w) (c.k' w) →+* ℂ := ι.comp (algebraMap _ _)

def ringOf (ι : KE c w →+* ℂ) : Subring ℂ := (ι.comp (algebraMap (c.Oe w) _)).range

def twVia (ρ : Setup D.ntw) (ι : KE c w →+* ℂ) : Twist D Circle :=
  twistOf ρ.rc (viaOk ι) (ρ.ch (c.twI w)) (c.Q w) (chr c w)

def Extends (ρ : Setup D.ntw) (ε : KE c w →+* ℂ) : Prop := viaOk ε = ρ.eOk (c.twI w) (c.sd w) (c.k' w)

theorem Extends.twVia_eq {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) :
    twVia ρ ε = ρ.tw (c.twI w) (c.sd w) (c.k' w) (c.Q w) (chr c w) := by
  rw [twVia, h]; rfl

theorem Extends.apply {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) (a : D.ntw.Ok (c.twI w) (c.k' w)) :
    ε (algebraMap _ _ a) = ρ.eOk (c.twI w) (c.sd w) (c.k' w) a := RingHom.congr_fun h a

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

def rdE (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) : Tgt c w (j.1 + 1) →ₛₗ[ε] Amb D j :=
  let φ : Tgt c w (j.1 + 1) →+ Amb D j := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp (T.rdV (c.k' w) (c.Q w) (chr c w)).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • T.rdV _ _ _ f = ε a • T.rdV _ _ _ (s • f)
      rw [← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) s f, LinearMap.map_smulₛₗ, Algebra.smul_def s a, map_mul, hε.apply,
        smul_smul, mul_comm]
      rfl
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ε (s • a) • T.rdV _ _ _ f = ε s • ε a • T.rdV _ _ _ f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdE_tmul (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdE T hε (a ⊗ₜ f) = ε a • T.rdV (c.k' w) (c.Q w) (chr c w) f := rfl

variable (rd) in

def rdF (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) :
    KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →ₛₗ[ε] (GA D (Wc D j) → ℂ) :=
  let φ : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • rd f = ε a • rd (s • f)
      rw [rd_smul, Algebra.smul_def s a, map_mul, IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply,
        hρ.ek_e, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ε (s • a) • rd f = ε s • ε a • rd f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdF_tmul (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdF rd hρ hε (a ⊗ₜ f) = ε a • rd f := rfl

end Choice

def ConjAt {j : Fin D.R.m} (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ) (τ : ℂ ≃+* ℂ) (F F' : Amb D j) : Prop :=
  ∀ h, ∃ x x' : VsV D j ℂ, ConjVec j τ x x' ∧ F h = Φ x ∧ F' h = Φ ((τ κ / κ) • x')

def intLL (D : D7) : Subring ℂ := (D.what₂.embLL.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)).range

theorem used_of_tw {w : D.what₂.places.Pl} (h : D.what₂.muAt w ≠ D.what₂.mu0) : Used0 D (D.what₂.muTw w) :=
  Or.inr ⟨w, ((D.what₂.muAt_or w).resolve_left h).symm⟩

section Rows

variable {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

def formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) : D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] (X.R.HV j (Y.tupT μ)).H :=
  (LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
    (Y.IL.jMt μ hμ j).toLinearMap

theorem extV_formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    X.R.toRealDat.extV j (Y.tupT μ) (formOf Y hμ j x) = (Y.IL.jMt μ hμ j x).1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).apply_symm_apply _)

def fockOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) :
    D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] Amb D j :=
  (X.R.ioP j (PiTensorProduct.tprod ℂ u)).compLeft _ ∘ₗ (X.R.HV j (Y.tupT μ)).e ∘ₗ formOf Y hμ j

theorem fockOf_apply {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (x h) :
    fockOf Y hμ j u x h = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j (Y.tupT μ)).e (formOf Y hμ j x) h) := rfl

variable (X) in

def IsLow (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : (X.R.MW j (sg0 D X.A3.A)).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ

variable {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl)
  (j : Fin D.R.m)

abbrev baseOf : Base (Vc D j) (Wc D j) := Z.ρ.B (c.twI w) j (c.sd w)

structure AtPlace : Prop where
  pins : GlobalTheory.Mem.R3.Pins X.R X.F X.cG
  intersectionNumber_baseChange : GlobalTheory.Mem.R3.Holds X.R X.F
  field : FieldOk X
  tw : D.what₂.muAt w ≠ D.what₂.mu0
  ok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)
  cls : ClsQ (D := D) (c.Q w)
  emb : ∀ ε : KE c w →+* ℂ, Extends Z.ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x
  val : ∀ σ, ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w))
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  ks : (S.A (j.1 + 1)).IsKsForm
  rat : RatRow YS X.geo.v₀ Z.good (c.twI w) j (c.sd w)
  tup : ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
    IsTupOf X.R.toRealDat (baseOf Z c w j) (twVia Z.ρ ι) (Y.tupT (D.what₂.muTw w))

end Rows

end GlobalTheory.PlaceRead

end
end
