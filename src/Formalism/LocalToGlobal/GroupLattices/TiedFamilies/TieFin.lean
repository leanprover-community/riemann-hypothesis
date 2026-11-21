import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieEvR
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieLatFin
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.GTiedFOfIsRecCEv
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecAct
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocIdFr
import Formalism.LocalToGlobal.HermitianForms.BothLemmas
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieTrF
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePsi

section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section C

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

set_option maxHeartbeats 4000000 in

theorem hypT_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    HypT ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg) :=
  hypT_of (hL u) _ (I u w hg) (levTieOf_fr (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg))
    (levTieOf_spl (hL u) (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg)) (isHyperbolicAt_rec_of_placeIdentification D u w hg (I u w hg))

end C

end Formalism.L2.G
end
end

section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

set_option maxHeartbeats 8000000 in

theorem ptOne_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    PtOne ((T u).cls0).lev ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) :=
  ptOne_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u hU w hg B (frRat_C D sc Ce Lc I ψ hd H0 hL B hB u w hg)
    (hypT_C D sc Ce Lc I ψ hd H0 hL u w hg)

set_option maxHeartbeats 8000000 in

theorem ex_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : EvRatRep (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL ((recC D sc Ce Lc I ψ hd).gat u w hg)
      (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u))
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T (gatTiesC D sc Ce Lc I ψ hd)
    (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) u w hg
    (ptOne_C D sc Ce Lc I ψ hd H0 hL T B hB u hU w hg) h1 h2

set_option maxHeartbeats 8000000 in

theorem ex_C_blk (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (u : D.what₂.Word) (hU : SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (h1 : BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B)
    (h2 : LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u) :
    ValEx ((T u).cls0).lev (embT (recC D sc Ce Lc I ψ hd)) (recC D sc Ce Lc I ψ hd).what₂.embLL
      ((recC D sc Ce Lc I ψ hd).gat u w hg) (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B)
      ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg) (embFr (D := recC D sc Ce Lc I ψ hd) T u) ((T u).cls0).y :=
  ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u hU w hg
    (evRatRep_rec (D := recC D sc Ce Lc I ψ hd) (X := hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T
      (gatTiesC D sc Ce Lc I ψ hd) u w hg B h1) h2

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)
  (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
  (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
  (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
    (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)

structure CmpLeft : Prop where
  same : ∀ u, SameUloc (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u
  blk : ∀ u w hg, BlockRationalityAtPlace (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) (gatTiesC D sc Ce Lc I ψ hd) u w hg B
  psi0 : ∀ u, LevelZeroCharacterRational (D := recC D sc Ce Lc I ψ hd) T u
  chi : ∀ u w hg i (γ : (((recC D sc Ce Lc I ψ hd).gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap ((recC D sc Ce Lc I ψ hd).gat u w hg).O ((recC D sc Ce Lc I ψ hd).gat u w hg).Kf
        ((((recC D sc Ce Lc I ψ hd).gat u w hg).lev i).χ γ : ((recC D sc Ce Lc I ψ hd).gat u w hg).O) *
          (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg r = 1
  valInt : ValIntRec T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB)

variable {D sc Ce Lc I ψ hd H0 hL T B hBs hB}

set_option maxHeartbeats 8000000 in

theorem CmpLeft.core (N : CmpLeft D sc Ce Lc I ψ hd H0 hL T B hBs hB)
    (pos : ∀ u w hg v (s : Fin (((recC D sc Ce Lc I ψ hd).gat u w hg).P.n' v)) (x : D.host.E),
      (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
        ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x))) :
    CmpCore T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) where
  same := N.same
  ex := fun u w hg => ex_C D sc Ce Lc I ψ hd H0 hL T B hBs hB u (N.same u) w hg
    (evRatRep_rec T (gatTiesC D sc Ce Lc I ψ hd) u w hg B (N.blk u w hg)) (N.psi0 u)
  pos := pos
  chi := N.chi

set_option maxHeartbeats 8000000 in

theorem CmpLeft.toHyp0P (N : CmpLeft D sc Ce Lc I ψ hd H0 hL T B hBs hB)
    (pos : ∀ u w hg v (s : Fin (((recC D sc Ce Lc I ψ hd).gat u w hg).P.n' v)) (x : D.host.E),
      (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg
        (tEL (recC D sc Ce Lc I ψ hd) ((gatTiesC D sc Ce Lc I ψ hd).gat_pos u w hg ⟨v, s⟩)
          (if Even s.val then x else sigD (recC D sc Ce Lc I ψ hd) x)) =
        ((recC D sc Ce Lc I ψ hd).gat u w hg).P.ι v ((((recC D sc Ce Lc I ψ hd).gat u w hg).P.σ v ^ s.val)
          ((locAt (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) u w hg B).iw v x))) :
    CmpHyp0P T (gatTiesC D sc Ce Lc I ψ hd) (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) :=
  cmpHyp0P_of_cmpCore (N.core pos)
    (fun u w hg => gatIs_recC D sc Ce Lc I ψ hd H0 hL (fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)) u w hg) N.valInt

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField Matrix

namespace Formalism.L2.G

theorem stdB_core {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (h : V → V → E)
    (c : V ≃ₗ[E] (Fin n → E)) (hc : ∀ x y, h x y = hform σ J (c x) (c y)) (b : Module.Basis (Fin n) E V)
    (hb : ∀ a a', h (b a) (b a') = if a = a' then 1 else 0) (L0 : Submodule (𝓞 E) V)
    (hL : L0 = Submodule.span (𝓞 E) (Set.range b)) :
    ∃ B : GL (Fin n) E, cT σ B.1 * J * B.1 = 1 ∧
      ∀ x : Fin n → E, x ∈ L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ↔
        ∀ a, ((B⁻¹ : GL (Fin n) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  let b' : Module.Basis (Fin n) E (Fin n → E) := b.map c
  let M : Matrix (Fin n) (Fin n) E := (Pi.basisFun E (Fin n)).toMatrix b'
  let M' : Matrix (Fin n) (Fin n) E := b'.toMatrix (Pi.basisFun E (Fin n))
  have h1 : M * M' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have h2 : M' * M = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  let B : GL (Fin n) E := ⟨M, M', h1, h2⟩
  have hM : ∀ i a, M i a = c (b a) i := fun i a => by
    simp [M, b', Module.Basis.toMatrix_apply]
  refine ⟨B, ?_, fun x => ?_⟩
  · ext a a'
    have := hb a a'
    rw [hc] at this
    rw [Matrix.one_apply, ← this]
    simp only [hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, B, hM, Finset.sum_mul]
    rw [Finset.sum_comm]
  · have e1 : L0.map ((c : V →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Submodule.span (𝓞 E) (Set.range b') := by
      rw [hL, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [e1, Module.Basis.mem_span_iff_repr_mem]
    have e2 : (B⁻¹ : GL (Fin n) E).1 *ᵥ x = b'.repr x := by
      show M' *ᵥ x = b'.repr x
      have h3 := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun E (Fin n)) b' x
      have h4 : ((Pi.basisFun E (Fin n)).repr x : Fin n → E) = x := funext fun i => Pi.basisFun_repr E (Fin n) x i
      rw [h4] at h3
      exact h3
    rw [e2]
    rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_form_frame_coordinates (D : D7) (x y : (D.sp.X 0).V) :
    (D.sp.X 0).hT x y = hform (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
      (crdN D 0 (Nat.zero_le _) x) (crdN D 0 (Nat.zero_le _) y) := by
  rw [Formalism.L2.Herm.hT_crd D.sp.cm]
  unfold hform
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← (finCongr (rankN D 0 (Nat.zero_le _))).sum_comp]
  rfl

theorem exists_stdB (D : D7) (h : Formalism.L2.Herm.IsStd (D.sp.X 0)) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B := by
  obtain ⟨b, hb, hL⟩ := h
  obtain ⟨B, h1, h2⟩ := stdB_core (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))
    (fun x y => (D.sp.X 0).hT x y) (crdN D 0 (Nat.zero_le _)) (hermitian_form_frame_coordinates D)
    (b.reindex (finCongr (rankN D 0 (Nat.zero_le _))))
    (fun a a' => by
      simp only [Module.Basis.reindex_apply]
      rw [hb]
      simp)
    (D.sp.X 0).L0 (by rw [hL, Module.Basis.range_reindex])
  refine ⟨(reGL (rank_eq_first_level D.R) D.host.E).symm B, ?_, ?_⟩
  · rw [MulEquiv.apply_symm_apply]
    exact h1
  · rw [MulEquiv.apply_symm_apply]
    exact h2

theorem exists_stdB_of_tied (D : D7) (h : Formalism.L2.Herm.StdTied D) : ∃ B : GL (Fin D.R.k) D.host.E, Cmp.StdB D B :=
  exists_stdB D (h.1 0 (Nat.zero_le _))

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.G

section Re

theorem reGL_mulVec {a b : ℕ} (h : a = b) {E : Type} [Field E] (M : GL (Fin a) E) (x : Fin a → E) (i : Fin b) :
    ((reGL h E M).1 *ᵥ fun j : Fin b => x (Fin.cast h.symm j)) i = (M.1 *ᵥ x) (Fin.cast h.symm i) := by
  subst h
  rw [reGL_rfl]
  rfl

end Re

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stdB_mem (D : D7) (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (x : Fin D.R.k → D.host.E) :
    x ∈ D.sp.crdLat0 (D.sp.X 0).L0 ↔
      ∀ a, ((B⁻¹ : GL (Fin D.R.k) D.host.E).1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h2 := hB.2 (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j))
  have e1 : (fun j => x (Fin.cast (rank_eq_first_level D.R).symm j)) ∈ selfDualLatticeCoords D 0 (Nat.zero_le _) ↔ x ∈ D.sp.crdLat0 (D.sp.X 0).L0 := by
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext a
      have := congrFun e (Fin.cast (rank_eq_first_level D.R) a)
      exact this
    · rintro ⟨v, hv, e⟩
      refine ⟨v, hv, ?_⟩
      funext j
      have := congrFun e (Fin.cast (rank_eq_first_level D.R).symm j)
      exact this
  rw [← e1, h2]
  constructor
  · intro h a
    have := h (Fin.cast (rank_eq_first_level D.R) a)
    rw [← map_inv, reGL_mulVec] at this
    exact this
  · intro h j
    rw [← map_inv, reGL_mulVec]
    exact h _

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
    {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem T_smul_mem (L : ColLevel R F E sp gp C A clsLat) (y : Fin R.k → E)
    (hy : y ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb)) : (A.T : E) • y ∈ L.Lb := by
  induction hy using Submodule.span_induction with
  | mem y hy => exact L.Lb_dual y hy
  | zero => rw [smul_zero]; exact L.Lb.zero_mem
  | add y z _ _ h1 h2 => rw [smul_add]; exact L.Lb.add_mem h1 h2
  | smul c y _ h => rw [smul_comm]; exact L.Lb.smul_mem c h

theorem companion_le (L : ColLevel R F E sp gp C A clsLat) (𝔞 : Ideal (𝓞 E)) :
    L.Lb ⊔ 𝔞 • Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) ≤
      Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb) :=
  sup_le (fun x hx => Submodule.subset_span (L.Lb_int x hx)) Submodule.smul_le_right

def LocId.withFr (I : LocId L p nV W Qq) (B : GL (Fin R.k) E)
    (h1 : ∀ x ∈ L.Lb, ∀ a, ((B⁻¹ : GL (Fin R.k) E).1 *ᵥ x) a ∈ (algebraMap (𝓞 E) E).range)
    (N : ℕ) (hN : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → (N : 𝓞 F) ∉ w.asIdeal)
    (h2 : ∀ i, (N : E) • (B.1 *ᵥ Pi.single i 1) ∈ L.Lb) : LocId L p nV W Qq :=
  { I with
    fr := fun w h => bc (((RingHom.fst _ _).comp (I.spl w h).toRingHom).comp (inclE (F := F) (w.adicCompletion F))) B
    fr_lat := fun w h t => Formalism.MainNotions.Gaps.Loc.fr_lat_of w (I.spl w h) (I.spl_alg w h) L.Lb B h1 N (hN w h) h2 t }

def locIdStd (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ} {W' Qq' : Type}
    [CommRing W'] [Field Qq'] [Algebra W' Qq'] (I : LocId Lc (D.what₂.places.resChar w) nV W' Qq')
    (B : GL (Fin D.R.k) D.host.E) (hB : Cmp.StdB D B) (𝔞 : Ideal (𝓞 D.host.E))
    (hL : Lc.Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E) (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 Lc.Lb) =
      D.sp.crdLat0 (D.sp.X 0).L0) : LocId Lc (D.what₂.places.resChar w) nV W' Qq' :=
  I.withFr B (fun x hx => (stdB_mem D B hB x).1 (hL ▸ (le_sup_left : Lc.Lb ≤ _) hx)) (D.mem u).A.T
    (fun w' hw' => natCast_notMem w' hg.1 hw' hg.2.2.2.2.2)
    (fun i => T_smul_mem Lc _ (companion_le Lc 𝔞 (hL ▸ (stdB_mem D B hB _).2 fun a => by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases h : a = i
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩)))



theorem companion_of_baseTied (D : D7) (H : Formalism.L2.Herm.HermCols D) (aT : ∀ u, Formalism.L2.Herm.AtT D u (H.vT u) (H.Fv u))
    (hb : Formalism.L2.Herm.BaseTied D H aT) (u : D.what₂.Word) :
    ∃ 𝔞 : Ideal (𝓞 D.host.E), (H.lev0 u).Lb ⊔ 𝔞 • Submodule.span (𝓞 D.host.E)
      (dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) D.sp.gram0 (H.lev0 u).Lb) = D.sp.crdLat0 (D.sp.X 0).L0 := by
  have hi : IsIntegral ℤ (D.host.conj ((aT u).piU : D.host.E)) :=
    map_isIntegral_int D.host.conj (RingOfIntegers.isIntegral_coe _)
  exact ⟨Ideal.span {(⟨_, hi⟩ : 𝓞 D.host.E)}, (hb u ⟨_, hi⟩ rfl).1⟩

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Herm Formalism.L2.Forms

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

def FullTiedNoG.cols {D : D7} (X : FullTiedNoG D) : ColsHerm D where
  base := X.base.toHermCols
  atT := X.atT
  levelZeroCompatibility := X.levelZeroCompatibility
  ad := X.ad
  cof := X.cof
  piG := X.piG
  stabMap := X.stabMap
  fvI := X.fvI
  std := X.std
  baseL := X.baseL

set_option maxHeartbeats 4000000 in

def colsHermSet (C : ColsHerm D) : ColsHerm (setGat D g' hd') where
  base := colsSet D g' hd' C.base
  atT := fun u => atTSet D g' hd' (C.atT u)
  levelZeroCompatibility := C.levelZeroCompatibility
  ad := adSet D g' hd' _ _ C.ad
  cof := C.cof
  piG := C.piG
  stabMap := C.stabMap
  fvI := C.fvI
  std := C.std
  baseL := C.baseL

set_option maxHeartbeats 8000000 in
theorem jointSet' (C : ColsHerm D) {u : D.what₂.Word} (T : FormsTied D u) (h : Joint C u T) :
    Joint (colsHermSet D g' hd' C) u (formsSet D g' hd' T) := { h with }

set_option maxHeartbeats 8000000 in

def columnsWithReplacedGroup (C : ColsTied D) : ColsTied (setGat D g' hd') where
  herm := colsHermSet D g' hd' C.herm
  forms := fun u => formsSet D g' hd' (C.forms u)
  joint := fun u => jointSet' D g' hd' C.herm (C.forms u) (C.joint u)
  gl_const := C.gl_const
  chi := C.chi
  fr_const := C.fr_const
  frP_const := C.frP_const

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Herm Formalism.L2.Forms Formalism.UG Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.factResChar

section Joints

variable (D : D7)
  (g' : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) → GAtP (D.what₂.places.resChar w))
  (hd' : ∀ u w h, (g' u w h).d = Module.finrank ℂ (D.mem u).A.Mu0)

end Joints

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))

section RecG

variable (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

def noG_recG (H : FullTiedNoG D) : FullTiedNoG (recG D sc Ce Lc X hd) := fullSet D _ hd H

def hermitianFormsOfRecursiveGroup (H : FullTiedNoG D) (hL : ∀ u, H.base.lev0 u = Lc u) : FullTied (recG D sc Ce Lc X hd) :=
  (noG_recG D sc Ce Lc X hd H).toFull fun u w hg => levTieOf (hL u) (levTieG D sc Ce Lc X hd u w hg)

def formsOfRecursiveGroup {u : D.what₂.Word} (T : Forms0 D u) : Forms0 (recG D sc Ce Lc X hd) u := forms0Set D _ hd T

end RecG

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G NumberField IsDedekindDomain

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Herm Formalism.L2.Forms Formalism.UG Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.factResChar

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev levelZeroHermitianTransport (H : FullTiedNoG D) (hL : ∀ u, H.base.lev0 u = Lc u) : Herm0 (recC D sc Ce Lc I ψ hd) :=
  (hermitianFormsOfRecursiveGroup D sc Ce Lc (packC D Lc I ψ) hd H hL).to0

abbrev formsOfRecursion (T : ∀ u : D.what₂.Word, Forms0 D u) : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u :=
  fun u => formsOfRecursiveGroup D sc Ce Lc (packC D Lc I ψ) hd (T u)

set_option maxHeartbeats 4000000 in

def secondLayerCompatibilities (H : FullTiedNoG D) (hL : ∀ u, H.base.lev0 u = Lc u) (T : ∀ u : D.what₂.Word, Forms0 D u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB D B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (CH : Cmp.CmpHyp (formsOfRecursion D sc Ce Lc I ψ hd T) (gatTiesC D sc Ce Lc I ψ hd)
      (cmpInC D sc Ce Lc I ψ hd (levelZeroHermitianTransport D sc Ce Lc I ψ hd H hL) hL B hBs hB)) :
    GroupCompatibilityAll (recC D sc Ce Lc I ψ hd) (gatTiesC D sc Ce Lc I ψ hd)
      (Cmp.latCmpC (formsOfRecursion D sc Ce Lc I ψ hd T) (gatTiesC D sc Ce Lc I ψ hd)
        (cmpInC D sc Ce Lc I ψ hd (levelZeroHermitianTransport D sc Ce Lc I ψ hd H hL) hL B hBs hB) CH) :=
  groupCompatibilityOfRecursion D sc Ce Lc I ψ hd (levelZeroHermitianTransport D sc Ce Lc I ψ hd H hL) hL (formsOfRecursion D sc Ce Lc I ψ hd T) B hBs hB CH
    fun u w h => isHyperbolicAt_rec_of_placeIdentification D u w h (I u w h)

end Formalism.L2.G
end
end

section
noncomputable section

namespace Formalism.L2.G

open Formalism.L2.G.Cmp Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

section Cast

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} {p : ℕ} {G : GAtP p}

theorem levTieOf_yG {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).yG = t.yG := by
  subst h
  rfl

theorem levTieOf_gamI {L L' : ColLevel R F E sp gp C A clsLat} (h : L' = L) (t : Formalism.L2.Herm.GLevTie L G) :
    (levTieOf h t).gamI = t.gamI := by
  subst h
  rfl

theorem gamToUp_val {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
    (σE : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E) (Up : Subgroup (GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : gamC σE J Up y) :
    (gamToUp σE J Up y γ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) =
      y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ) * y := by
  show (MulAut.conj y⁻¹) (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (gamMat σE J Up y γ)) = _
  rw [MulAut.conj_apply, inv_inv]

end Cast

def ChiClause {D : D7} {X : Formalism.L2.Herm.Herm0 D} (T : ∀ u : D.what₂.Word, Forms0 D u) (I : CmpIn D X) : Prop :=
  ∀ u w hg i (γ : ((D.gat u w hg).lev i).Γ) (κ : ((T u).cls0).lev.U),
    (locAt X u w hg I.B).IsAway i γ κ.1 →
    ∃ r : D.what₂.LL, D.what₂.embLL r = (((T u).cls0).lev.chi κ : ℂ) ∧
      algebraMap (D.gat u w hg).O (D.gat u w hg).Kf (((D.gat u w hg).lev i).χ γ : (D.gat u w hg).O) * I.embW u w hg r = 1

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

set_option maxHeartbeats 8000000 in

theorem chi_C (H0 : Formalism.L2.Herm.Herm0 (recC D sc Ce Lc I ψ hd)) (hL : ∀ u, H0.lev0 u = Lc u)
    (T : ∀ u : D.what₂.Word, Forms0 (recC D sc Ce Lc I ψ hd) u)
    (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB (recC D sc Ce Lc I ψ hd) B)
    (hB : ∀ u w hg (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal),
      (I u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((I u w hg).spl w' h).toRingHom).comp
        (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B)
    (hψ : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
        (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
        ((T u).cls0).lev (Lc u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
        ((cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB).embW u w hg) (ψ u w hg)) :
    ChiClause T (cmpInC D sc Ce Lc I ψ hd H0 hL B hBs hB) := by
  intro u w hg i γ κ hκ
  refine chi_rec (hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL) T u w hg B _ (Lc u) (hL u) (ψ u w hg) ?_ (hψ u w hg) i γ κ hκ
  intro i γ a ha
  have e1 : ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).yG = (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg).yG :=
    levTieOf_yG (hL u) _
  have e2 : ((hermitianLevelZeroOfRecursion D sc Ce Lc I ψ hd H0 hL).g u w hg).gamI = (levTieG D sc Ce Lc (packC D Lc I ψ) hd u w hg).gamI :=
    levTieOf_gamI (hL u) _
  rw [e1, e2] at ha
  have e3 : a = gamToUp D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w))
      (repP (Lc u) (D.what₂.places.resChar w) i : GL (Fin D.R.k) _) γ :=
    Subtype.ext (ha.trans (gamToUp_val _ _ _ _ γ).symm)
  rw [e3]
  rfl

end Formalism.L2.G
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms Formalism.L2.G.Cmp Formalism.L2.Herm

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

variable (D : D7) (H : FullTiedNoG D)
  (I0 : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))))
  (B : GL (Fin D.R.k) D.host.E) (hBs : Cmp.StdB D B)

def idStd : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (H.base.lev0 u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (nFr D (D.what₂.places.resChar w))) :=
  fun u w hg => locIdStd D u w hg (I0 u w hg) B hBs
    (Classical.choose (companion_of_baseTied D H.base.toHermCols H.atT H.baseL u))
    (Classical.choose_spec (companion_of_baseTied D H.base.toHermCols H.atT H.baseL u))

theorem idStd_fr (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal) :
    (idStd D H I0 B hBs u w hg).fr w' h = bc (((RingHom.fst _ _).comp ((idStd D H I0 B hBs u w hg).spl w' h).toRingHom).comp
      (inclE (F := D.host.F) (w'.adicCompletion D.host.F))) B := rfl

variable (sc : Scale) (Ce : ℝ) (T : ∀ u : D.what₂.Word, Forms0 D u)
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (H.base.lev0 u) (D.what₂.places.resChar w) →* (ORec D w (nFr D (D.what₂.places.resChar w)))ˣ)
  (hd : ∀ u w h, ((packC D (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

structure LeftD : Prop where

  joint : ∀ u, Joint0 H.base.lev0 u (T u)

  blk : ∀ u w hg, BlockRationalityAtPlace (levelZeroHermitianTransport D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd H (fun _ => rfl)) (gatTiesC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd) u w hg B

  psi0 : ∀ u, LevelZeroCharacterRational (D := recC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd) (formsOfRecursion D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd T) u

  psi : ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    PsiTied (LL := D.what₂.LL) (O := ORec D w (nFr D (D.what₂.places.resChar w)))
      (Kf := KfRec D w (nFr D (D.what₂.places.resChar w)))
      (((formsOfRecursion D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd T) u).cls0).lev (H.base.lev0 u) (D.what₂.places.resChar w) (rank_eq_first_level D.R) D.what₂.embLL
      ((cmpInC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd (levelZeroHermitianTransport D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd H (fun _ => rfl)) (fun _ => rfl) B hBs (idStd_fr D H I0 B hBs)).embW u w hg) (ψ u w hg)

  valInt : ValIntRec (formsOfRecursion D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd T) (gatTiesC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd) (cmpInC D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd (levelZeroHermitianTransport D sc Ce (fun u => H.base.lev0 u) (idStd D H I0 B hBs) ψ hd H (fun _ => rfl)) (fun _ => rfl) B hBs (idStd_fr D H I0 B hBs))

variable {D H I0 B hBs sc Ce T ψ hd}

end Formalism.L2.G
end
end
