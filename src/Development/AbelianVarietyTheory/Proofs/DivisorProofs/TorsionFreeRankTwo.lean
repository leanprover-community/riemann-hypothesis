import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracIdExistsTotPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionFiniteEtaleAbelianVarietyCharZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExistsSmallMemIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatLevelOf

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.DiagPull

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}}

def pairCls (X : Obj F 𝔠 S) (c : 𝔠.elt) {T : Over S} (u v : T ⟶ X.A) : GlobalTheory.CechPic.Pic T.left :=
  GlobalTheory.CechPic.pull (lift u v).left (cls (X.P c) (X.isLB c))

theorem pairCls_comp (X : Obj F 𝔠 S) (c : 𝔠.elt) {T T' : Over S} (g : T' ⟶ T) (u v : T ⟶ X.A) :
    GlobalTheory.CechPic.pull g.left (pairCls X c u v) = pairCls X c (g ≫ u) (g ≫ v) := by
  unfold pairCls
  rw [← comp_lift, Over.comp_left]
  exact (GlobalTheory.CechPic.pull_comp _ _ _).symm

theorem pairCls_symm (X : Obj F 𝔠 S) (c : 𝔠.elt) {T : Over S} (u v : T ⟶ X.A) :
    pairCls X c u v = pairCls X c v u := by
  have h : cls (X.P c) (X.isLB c) = pairCls X c (snd X.A X.A) (fst X.A X.A) :=
    (cls_eq_iff (X.isLB c) (pull_isLB (X.isLB c) _)).2 (X.symm c)
  have h2 := pairCls_comp X c (lift u v) (snd X.A X.A) (fst X.A X.A)
  rw [lift_fst, lift_snd] at h2
  exact (congrArg (GlobalTheory.CechPic.pull (lift u v).left) h).trans h2

theorem pairCls_smul (X : Obj F 𝔠 S) (a : 𝓞 F) (c : 𝔠.elt) {T : Over S} (u v : T ⟶ X.A) :
    pairCls X (a • c) u v = pairCls X c u (v ≫ X.rm.act a) := by
  have h : cls (X.P (a • c)) (X.isLB _) = pairCls X c (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) :=
    (cls_eq_iff (X.isLB _) (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  have h2 := pairCls_comp X c (lift u v) (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a)
  rw [lift_fst, lift_snd_assoc] at h2
  exact (congrArg (GlobalTheory.CechPic.pull (lift u v).left) h).trans h2

theorem pull_act_cls_diag {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S)
    (b : 𝓞 F) (c : 𝔠.elt) :
    GlobalTheory.CechPic.pull (X.rm.act b).left (cls (X.diag c) (pull_isLB (X.isLB c) _)) =
      cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) := by
  change GlobalTheory.CechPic.pull (X.rm.act b).left (pairCls X c (𝟙 _) (𝟙 _)) = pairCls X ((b * b) • c) (𝟙 _) (𝟙 _)
  rw [pairCls_comp, mul_smul, pairCls_smul, pairCls_symm X (b • c), pairCls_smul, Category.comp_id,
    Category.id_comp]

end GlobalTheory.RealMult.DiagPull
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_mult_pullback_polarization_class : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S) (b : 𝓞 F) (c : 𝔠.elt), GlobalTheory.CechPic.pull (X.rm.act b).left (cls (X.diag c) (pull_isLB (X.isLB c) _)) = cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) := by
  atlas_forward_decl GlobalTheory.RealMult.DiagPull.pull_act_cls_diag
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OActFinEtNorm

theorem dvd_natAbs_norm {E : Type} [Field E] [NumberField E] (b : 𝓞 E) :
    b ∣ (((Algebra.norm ℤ b).natAbs : ℕ) : 𝓞 E) := by
  rw [← Ideal.absNorm_span_singleton]
  exact Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)

theorem finite_etale_act_of_norm {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {Ω : Type}
    [Field Ω] [IsAlgClosed Ω] (X : Obj F 𝔠 (Sp Ω)) (b : 𝓞 F)
    (hb : ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0) :
    IsFinite (X.rm.act b).left ∧ Etale (X.rm.act b).left ∧
      Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} := by
  have hA := X.ab
  have hg := X.dim
  haveI := hA.comm
  haveI := hA.smooth
  haveI := hA.proper
  set n : ℕ := (Algebra.norm ℤ b).natAbs with hn_def
  obtain ⟨b', hb'⟩ := dvd_natAbs_norm b
  have hnk : (n : Ω) ≠ 0 := by
    intro h
    apply hb
    rcases Int.natAbs_eq (Algebra.norm ℤ b) with h' | h'
    · rw [h', Int.cast_natCast]; exact h
    · rw [h', Int.cast_neg, Int.cast_natCast, h, neg_zero]
  have hu : IsUnit (n : Γ(Sp Ω, ⊤)) := by
    simpa using (Ne.isUnit hnk).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  have h1 : X.rm.act b ≫ X.rm.act b' = 𝟙 X.A ^ n := by
    rw [← X.rm.mul, ← hb', GlobalTheory.OActFinEt.act_natCast]
  haveI := X.rm.hom b
  haveI := X.rm.hom b'
  haveI hF : IsFinite (𝟙 X.A ^ n).left := GrpTangent.isFinite_id_pow X.A hu
  haveI hE : Etale (𝟙 X.A ^ n).left := GrpTangent.etale_id_pow X.A hu
  have hsep : ∀ f : X.A ⟶ X.A, IsSeparated f.left := fun f => by
    have : IsSeparated (f.left ≫ X.A.hom) := by rw [Over.w f]; infer_instance
    exact IsSeparated.of_comp f.left X.A.hom
  haveI := hsep (X.rm.act b')
  haveI : IsFinite ((X.rm.act b).left ≫ (X.rm.act b').left) := by
    rw [← Over.comp_left, h1]; exact hF
  haveI hfin : IsFinite (X.rm.act b).left := IsFinite.of_comp _ (X.rm.act b').left
  haveI : FormallyUnramified ((X.rm.act b).left ≫ (X.rm.act b').left) := by
    rw [← Over.comp_left, h1]; infer_instance
  haveI : FormallyUnramified (X.rm.act b).left := FormallyUnramified.of_comp _ (X.rm.act b').left
  haveI : Flat (X.rm.act b).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected Ω X.A hA _ inferInstance
      hfin).1
  haveI : LocallyOfFinitePresentation ((X.rm.act b).left ≫ X.A.hom) := by
    rw [Over.w]; infer_instance
  haveI : LocallyOfFinitePresentation (X.rm.act b).left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp _ X.A.hom
  refine ⟨hfin, Etale.of_formallyUnramified_of_flat _, ?_⟩
  have hfinN := GlobalTheory.Published.AbMulNSt.finite GlobalTheory.abMulN_holds hA hg hnk
  refine Finite.of_injective (β := {x : 𝟙_ (Over (Sp Ω)) ⟶ X.A // x ^ n = 1})
    (fun x => ⟨x.1, ?_⟩) ?_
  · have := congrArg (· ≫ X.rm.act b') x.2
    simp only [Category.assoc, h1, one_comp] at this
    rwa [comp_pow, Category.comp_id] at this
  · intro x y h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext h

end GlobalTheory.OActFinEtNorm
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_mult_isogeny_finite_etale : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {Ω : Type} [Field Ω] [IsAlgClosed Ω] (X : Obj F 𝔠 (Sp Ω)) (b : 𝓞 F), ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 → IsFinite (X.rm.act b).left ∧ Etale (X.rm.act b).left ∧ Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} := by
  atlas_forward_decl GlobalTheory.OActFinEtNorm.finite_etale_act_of_norm
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TensMul

variable {K : Type} [Field K] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of K))

def mulSec {L D : LB Y} (s : LB.Sec D) (σ : LB.Sec L) : LB.Sec (tens L D) where
  f := fun p : L.ι × D.ι => rs Y (inf_le_left : L.U p.1 ⊓ D.U p.2 ≤ L.U p.1) (σ.f p.1) *
      rs Y (inf_le_right : L.U p.1 ⊓ D.U p.2 ≤ D.U p.2) (s.f p.2)
  compat := fun (p q : L.ι × D.ι) => by
    obtain ⟨i, j⟩ := p
    obtain ⟨k, l⟩ := q
    have c₁ : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U i ⊓ L.U k :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have c₂ : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ D.U j ⊓ D.U l :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have h₁ : rs Y (inf_le_left : L.U i ⊓ L.U k ≤ L.U i) (σ.f i) =
        (L.g i k).val * rs Y (inf_le_right : L.U i ⊓ L.U k ≤ L.U k) (σ.f k) := σ.compat i k
    have h₂ : rs Y (inf_le_left : D.U j ⊓ D.U l ≤ D.U j) (s.f j) =
        (D.g j l).val * rs Y (inf_le_right : D.U j ⊓ D.U l ≤ D.U l) (s.f l) := s.compat j l
    have h₁' := congrArg (rs Y c₁) h₁
    have h₂' := congrArg (rs Y c₂) h₂
    rw [map_mul, rs_rs, rs_rs] at h₁' h₂'
    change rs Y (inf_le_left : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U i ⊓ D.U j)
        (rs Y (inf_le_left : L.U i ⊓ D.U j ≤ L.U i) (σ.f i) * rs Y (inf_le_right : L.U i ⊓ D.U j ≤ D.U j) (s.f j)) =
      (rs Y c₁ (L.g i k).val * rs Y c₂ (D.g j l).val) *
        rs Y (inf_le_right : L.U i ⊓ D.U j ⊓ (L.U k ⊓ D.U l) ≤ L.U k ⊓ D.U l)
          (rs Y (inf_le_left : L.U k ⊓ D.U l ≤ L.U k) (σ.f k) * rs Y (inf_le_right : L.U k ⊓ D.U l ≤ D.U l) (s.f l))
    rw [map_mul, map_mul, rs_rs, rs_rs, rs_rs, rs_rs, h₁', h₂']
    ring

def mulLin {L D : LB Y} (s : LB.Sec D) : SecOnR f L ⊤ →ₗ[K] SecOnR f (tens L D) ⊤ :=
  GlobalTheory.VeryAmpleGrowth.linTop f (fun a => mulSec s (SecOnR.topEquiv f L a))
    (fun a b (p : L.ι × D.ι) => by
      change @Eq Γ(Y, L.U p.1 ⊓ D.U p.2) (rs Y _ ((SecOnR.topEquiv f L (a + b)).f p.1) * rs Y inf_le_right (s.f p.2))
        (rs Y inf_le_left ((SecOnR.topEquiv f L a).f p.1) * rs Y inf_le_right (s.f p.2) +
          rs Y inf_le_left ((SecOnR.topEquiv f L b).f p.1) * rs Y inf_le_right (s.f p.2))
      rw [GlobalTheory.VeryAmpleGrowth.top_add, map_add]
      exact add_mul _ _ _)
    (fun c a (p : L.ι × D.ι) => by
      change @Eq Γ(Y, L.U p.1 ⊓ D.U p.2) (rs Y inf_le_left ((SecOnR.topEquiv f L (c • a)).f p.1) * rs Y inf_le_right (s.f p.2))
        (cst f (L.U p.1 ⊓ D.U p.2) c * (rs Y (inf_le_left : L.U p.1 ⊓ D.U p.2 ≤ L.U p.1) ((SecOnR.topEquiv f L a).f p.1) *
          rs Y (inf_le_right : L.U p.1 ⊓ D.U p.2 ≤ D.U p.2) (s.f p.2)))
      rw [GlobalTheory.VeryAmpleGrowth.top_smul, map_mul, rs_cst]
      exact _root_.mul_assoc _ _ _)

theorem top_mulLin {L D : LB Y} (s : LB.Sec D) (a : SecOnR f L ⊤) :
    SecOnR.topEquiv f (tens L D) (mulLin f s a) = mulSec s (SecOnR.topEquiv f L a) :=
  GlobalTheory.VeryAmpleGrowth.top_linTop f _ _ _ a

theorem mulLin_injective [IsIntegral Y] {L D : LB Y} (hL : L.IsLB) (s : LB.Sec D) {x : Y}
    (hx : x ∈ Out.nonzeroLocus s) : Function.Injective (mulLin f (L := L) s) := by
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hxL : x ∈ ⨆ i, L.U i := by rw [hL.cover]; trivial
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hxL
  let W : Y.Opens := L.U i₀ ⊓ Y.basicOpen (s.f j₀)
  have hWB : W ≤ Y.basicOpen (s.f j₀) := inf_le_right
  have hBD : Y.basicOpen (s.f j₀) ≤ D.U j₀ := Y.basicOpen_le _
  have hWL : W ≤ L.U i₀ := inf_le_left
  have hWT : W ≤ L.U i₀ ⊓ D.U j₀ := le_inf hWL (hWB.trans hBD)
  haveI : Nonempty W := ⟨⟨x, hi₀, hj₀⟩⟩
  have hu : IsUnit (rs Y (hWB.trans hBD) (s.f j₀)) := by
    rw [← rs_rs hBD hWB]
    exact (Y.toRingedSpace.isUnit_res_basicOpen (s.f j₀)).map _
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  have h : (mulSec s (SecOnR.topEquiv f L a)).f (i₀, j₀) = 0 := by
    have e := top_mulLin f s a
    rw [ha] at e
    exact (congrArg (fun σ : LB.Sec (tens L D) => σ.f (i₀, j₀)) e).symm.trans
      (GlobalTheory.VeryAmpleGrowth.top_zero f (M := tens L D) (i₀, j₀))
  have h' := congrArg (rs Y hWT) h
  change rs Y hWT (rs Y (inf_le_left : L.U i₀ ⊓ D.U j₀ ≤ L.U i₀) ((SecOnR.topEquiv f L a).f i₀) *
    rs Y (inf_le_right : L.U i₀ ⊓ D.U j₀ ≤ D.U j₀) (s.f j₀)) = rs Y hWT 0 at h'
  rw [map_mul, map_zero, rs_rs, rs_rs, hu.mul_left_eq_zero] at h'
  exact GlobalTheory.VeryAmpleGrowth.top_ext f fun k =>
    (GlobalTheory.SecGrowth.sec_eq_zero (M := L) (SecOnR.topEquiv f L a) (k₀ := i₀) hWL h' k).trans
      (GlobalTheory.VeryAmpleGrowth.top_zero f k).symm

end GlobalTheory.TensMul

theorem GlobalTheory.TensMul.finite_finrank_le_tens : ∀ {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) {L D : LB Y}, L.IsLB → D.IsLB → ∀ (s : LB.Sec D) {x : Y}, x ∈ Out.nonzeroLocus s → Module.Finite K (SecOnR f (tens L D) ⊤) → Module.Finite K (SecOnR f L ⊤) ∧ Module.finrank K (SecOnR f L ⊤) ≤ Module.finrank K (SecOnR f (tens L D) ⊤) := by
  intro K _ Y _ f L D hL _ s x hx hfin
  have hinj := GlobalTheory.TensMul.mulLin_injective f hL s hx
  exact ⟨Module.Finite.of_injective _ hinj, LinearMap.finrank_le_finrank_of_injective hinj⟩
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_sections_mono_tensor_effective : ∀ {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) {L D : LB Y}, L.IsLB → D.IsLB → ∀ (s : LB.Sec D) {x : Y}, x ∈ Out.nonzeroLocus s → Module.Finite K (SecOnR f (tens L D) ⊤) → Module.Finite K (SecOnR f L ⊤) ∧ Module.finrank K (SecOnR f L ⊤) ≤ Module.finrank K (SecOnR f (tens L D) ⊤) := by
  atlas_forward_decl GlobalTheory.TensMul.finite_finrank_le_tens
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowSecNonzero

def oneSec {Y : Scheme.{0}} (H : LB Y) : LB.Sec (pw H ((0 : ℕ) : ℤ)) where
  f := fun _ => 1
  compat := fun k l => by
    change rs Y (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) 1 =
      (H.g k l ^ ((0 : ℕ) : ℤ)).val * rs Y (inf_le_right : H.U k ⊓ H.U l ≤ H.U l) 1
    simp

def powSec {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (u : ℕ) : LB.Sec (pw H (u : ℤ)) :=
  Nat.rec (motive := fun u : ℕ => LB.Sec (pw H (u : ℤ))) (oneSec H)
    (fun u σ => GlobalTheory.VeryAmpleGrowth.mulPw s u σ) u

theorem powSec_f {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι) :
    ∀ u : ℕ, (show Γ(Y, H.U k) from (powSec s u).f k) = s.f k ^ u
  | 0 => by simp [powSec, oneSec]; rfl
  | u + 1 => by
    change s.f k * (show Γ(Y, H.U k) from (powSec s u).f k) = s.f k ^ (u + 1)
    rw [powSec_f s k u, pow_succ, mul_comm]

theorem exists_pw_sec_nonzero : ∀ {Y : Scheme.{0}} {D : LB Y} {J : Type} (s : J → LB.Sec D) (i : J) {x : Y}, x ∈ Out.nonzeroLocus (s i) → ∀ u : ℕ, ∃ σ : LB.Sec (pw D u), x ∈ Out.nonzeroLocus σ := by
  intro Y D J s i x hx u
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨powSec (s i) u, TopologicalSpace.Opens.mem_iSup.2 ⟨k₀, ?_⟩⟩
  have e := powSec_f (s i) k₀ u
  change x ∈ Y.basicOpen (show Γ(Y, D.U k₀) from (powSec (s i) u).f k₀)
  rw [e]
  cases u with
  | zero =>
    rw [pow_zero, Scheme.basicOpen_of_isUnit _ isUnit_one]
    exact Y.basicOpen_le _ hk₀
  | succ n => rw [Scheme.basicOpen_pow _ _ (Nat.succ_pos n)]; exact hk₀

end GlobalTheory.PowSecNonzero
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_power_nonvanishing : ∀ {Y : Scheme.{0}} {D : LB Y} {J : Type} (s : J → LB.Sec D) (i : J) {x : Y}, x ∈ Out.nonzeroLocus (s i) → ∀ u : ℕ, ∃ σ : LB.Sec (pw D u), x ∈ Out.nonzeroLocus σ := by
  atlas_forward_decl GlobalTheory.PowSecNonzero.exists_pw_sec_nonzero
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem le_of_frequently_mul_pow_le_mul_add_pow :
    ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := by
  intro d D a f h
  by_contra hlt
  push_neg at hlt
  have hq : Filter.Tendsto (fun s : ℕ => ((s:ℝ) + a) / s) Filter.atTop (nhds 1) := by
    have h2 : Filter.Tendsto (fun s : ℕ => 1 + (a:ℝ) / s) Filter.atTop (nhds (1 + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (a:ℝ))
    rw [add_zero] at h2
    apply h2.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with s hs
    have hs' : (s:ℝ) ≠ 0 := by positivity
    rw [add_div, div_self hs']
  have h1 : Filter.Tendsto (fun s : ℕ => (D:ℝ) * (((s:ℝ) + a) / s) ^ f) Filter.atTop
      (nhds ((D:ℝ) * 1 ^ f)) := tendsto_const_nhds.mul (hq.pow f)
  rw [one_pow, _root_.mul_one] at h1
  have hd : (D:ℝ) < d := by exact_mod_cast hlt
  have hev : ∀ᶠ s : ℕ in Filter.atTop, (D:ℝ) * (((s:ℝ) + a) / s) ^ f < d :=
    h1.eventually (gt_mem_nhds hd)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨s, hs, hle⟩ := h (N + 1)
  have hlt2 := hN s (by omega)
  have hspos : (0:ℝ) < s := by
    have : 0 < s := by omega
    exact_mod_cast this
  rw [div_pow, mul_div_assoc', div_lt_iff₀ (by positivity)] at hlt2
  have hc : ((d * s ^ f : ℕ) : ℝ) ≤ ((D * (s + a) ^ f : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at hc
  linarith

example : ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := le_of_frequently_mul_pow_le_mul_add_pow

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_of_eventual_polynomial_growth : ∀ (d D a f : ℕ), (∀ N : ℕ, ∃ s, N ≤ s ∧ d * s ^ f ≤ D * (s + a) ^ f) → d ≤ D := by
  atlas_forward_decl GlobalTheory.le_of_frequently_mul_pow_le_mul_add_pow
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.RealMultKernel

theorem cls_diag_add {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S) (c c' : 𝔠.elt) :
    cls (X.diag (c + c')) (pull_isLB (X.isLB _) _) =
      cls (X.diag c) (pull_isLB (X.isLB _) _) + cls (X.diag c') (pull_isLB (X.isLB _) _) := by
  have e : cls (X.P c') (X.isLB c') = cls (X.P (c + c')) (X.isLB _) - cls (X.P c) (X.isLB c) := by
    rw [← cls_div (X.isLB _) (X.isLB _) (LB.isLB_div (X.isLB _) (X.isLB _))]
    exact (cls_eq_iff _ _).2 (X.add c c')
  show CechPic.pull _ (cls (X.P (c + c')) (X.isLB _)) =
    CechPic.pull _ (cls (X.P c) (X.isLB c)) + CechPic.pull _ (cls (X.P c') (X.isLB c'))
  rw [e, map_sub]; abel

theorem cls_diag_natCast_smul {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S : Scheme.{0}} (X : Obj F 𝔠 S)
    (c : 𝔠.elt) (n : ℕ) :
    cls (X.diag ((n : 𝓞 F) • c)) (pull_isLB (X.isLB _) _) = n • cls (X.diag c) (pull_isLB (X.isLB _) _) := by
  induction n with
  | zero =>
    have h := cls_diag_add X 0 0
    simp only [add_zero] at h
    simp only [Nat.cast_zero, zero_smul]
    exact left_eq_add.1 h
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, cls_diag_add, ih, succ_nsmul]

theorem card_ker_act_le : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (X : Obj F 𝔠 (Sp Ω)), ∃ C : ℕ, ∀ (b : 𝓞 F) (k : ℕ), ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 →
      IsTotPos (((k : F)) ^ 2 - (b : F) ^ 2) →
      Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} ∧
      Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} ≤ C * k ^ (2 * Module.finrank ℚ F) := by
  intro F _ _ _ 𝔠 Ω _ _ X
  have hB := X.ab
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral X.A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral X.A.left := GeometricallyIntegral.isIntegral_of_subsingleton X.A.hom
  obtain ⟨c, hc⟩ := fracId_exists_totPos F 𝔠
  have hLc : (X.diag c).IsLB := pull_isLB (X.isLB c) _
  obtain ⟨m, hm, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy Ω X.A (X.diag c) hLc).1 (X.pos c hc)
  have hH : (pw (X.diag c) m).IsLB := isLB_pw hLc _
  obtain ⟨hfin, -, c₀, C₀, -, hgrow⟩ :=
    GlobalTheory.VeryAmpleGrowth.finite_monotone_growth Ω X.A.left X.A.hom _ X.dim _ n s hH hs
  refine ⟨c₀ * C₀, fun b k hb hpos => ?_⟩
  obtain ⟨hfinφ, hetφ, hker⟩ := GlobalTheory.T.real_mult_isogeny_finite_etale X b hb
  refine ⟨hker, ?_⟩
  have hcard := GlobalTheory.finrank_eq_card_kernel_points_of_etale Ω X.A hB (X.rm.act b)
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exfalso
      obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
      have h0 := hpos (v.embedding_of_isReal (IsTotallyReal.isReal v))
      simp at h0
      nlinarith [sq_nonneg ((v.embedding_of_isReal (IsTotallyReal.isReal v)) (b : F))]
    · exact h
  set e : 𝓞 F := (k : 𝓞 F) ^ 2 - b ^ 2 with he
  have hce : IsTotPos (((e • c : 𝔠.elt)) : F) := by
    intro τ
    have h1 := hpos τ
    have h2 := hc τ
    have h3 : (((e • c : 𝔠.elt)) : F) = ((k : F) ^ 2 - (b : F) ^ 2) * (c : F) := by
      rw [Submodule.coe_smul, Algebra.smul_def, he]
      first | simp | (push_cast; norm_cast) | (congr 1; simp)
    rw [h3, map_mul]
    exact mul_pos h1 h2
  have hDe : (X.diag (e • c)).IsLB := pull_isLB (X.isLB _) _
  obtain ⟨m', hm', n', s', hs'⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy Ω X.A _ hDe).1 (X.pos _ hce)
  obtain ⟨x₀⟩ : Nonempty X.A.left := inferInstance
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show x₀ ∈ ⨆ i, Out.nonzeroLocus (s' i) by rw [hs'.1]; trivial)
  obtain ⟨n'', s'', hs''⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw Ω X.A.left X.A.hom _ n s hH hs m' hm'
  have hsum : cls (X.diag ((b * b) • c)) (pull_isLB (X.isLB _) _) + cls (X.diag (e • c)) (pull_isLB (X.isLB _) _) =
      (k ^ 2 : ℕ) • cls (X.diag c) (pull_isLB (X.isLB _) _) := by
    rw [← cls_diag_add, ← add_smul, ← cls_diag_natCast_smul]
    congr 3
    rw [he]; push_cast; ring
  have hφ : (X.rm.act b).left ≫ X.A.hom = X.A.hom := Over.w _
  have key : ∀ t : ℕ,
      Module.Finite Ω (SecOnR ((X.rm.act b).left ≫ X.A.hom)
        ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left) ⊤) ∧
      Module.finrank Ω (SecOnR ((X.rm.act b).left ≫ X.A.hom)
        ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left) ⊤) ≤
        Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)) ⊤) := by
    intro t
    rw [hφ]
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_section_power_nonvanishing s' i₀ hi₀ (m * t)
    have hLp : ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left).IsLB :=
      pull_isLB (isLB_pw (isLB_pw hH _) _) _
    have hD2 : (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ)).IsLB := isLB_pw (isLB_pw hDe _) _
    have hT : (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)).IsLB := isLB_pw hH _
    have hiso : LBIso (tens ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left)
        (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ))) (pw (pw (X.diag c) m) ((k ^ 2 * (m' * t) : ℕ) : ℤ)) := by
      rw [← cls_eq_iff (isLB_tens hLp hD2) hT, cls_tens hLp hD2,
        cls_pull (isLB_pw (isLB_pw hH _) _), GlobalTheory.AmpleStabFinite.cls_pw (isLB_pw hH _),
        GlobalTheory.AmpleStabFinite.cls_pw hH, GlobalTheory.AmpleStabFinite.cls_pw hLc, GlobalTheory.AmpleStabFinite.cls_pw (isLB_pw hDe _),
        GlobalTheory.AmpleStabFinite.cls_pw hDe, GlobalTheory.AmpleStabFinite.cls_pw hH, GlobalTheory.AmpleStabFinite.cls_pw hLc,
        map_zsmul, map_zsmul, map_zsmul, GlobalTheory.T.real_mult_pullback_polarization_class,
        eq_sub_of_add_eq hsum]
      push_cast
      module
    obtain ⟨w, hw⟩ := hiso
    have eqv := SecOnR.linEquiv X.A.hom (SecOn.congr (isLB_tens hLp hD2) hT w hw ⊤)
    haveI := hfin (k ^ 2 * (m' * t))
    haveI : Module.Finite Ω (SecOnR X.A.hom (tens ((pw (pw (pw (X.diag c) m) m') t).pull (X.rm.act b).left)
        (pw (pw (X.diag (e • c)) m') ((m * t : ℕ) : ℤ))) ⊤) := Module.Finite.equiv eqv.symm
    obtain ⟨h1, h2⟩ := GlobalTheory.T.finrank_sections_mono_tensor_effective X.A.hom hLp hD2 σ hσ inferInstance
    exact ⟨h1, h2.trans eqv.finrank_eq.le⟩
  have hpw : ∀ t : ℕ, pw (pw (pw (X.diag c) m) m') (t : ℤ) = pw (pw (X.diag c) m) ((m' * t : ℕ) : ℤ) := fun t => by
    rw [GlobalTheory.UU.TorsionCount.pw_pw, Nat.cast_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.finrank_sec_pull_sandwich Ω X.A.left X.A.left X.A.hom (X.rm.act b).left
    (pw (pw (X.diag c) m) m') n'' s'' (isLB_pw hH _) hs'' _ hcard (fun t => by rw [hpw]; exact hfin _)
    (fun t => (key t).1)
  refine GlobalTheory.T.le_of_eventual_polynomial_growth _ _ a (Module.finrank ℚ F) fun N => ⟨max N 1, le_max_left _ _, ?_⟩
  set s₁ := max N 1 with hs₁
  have hs1 : 1 ≤ s₁ := le_max_right _ _
  have g1 := (hgrow (m' * s₁) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))).1
  have g2 := (ha s₁).1
  rw [hpw] at g2
  have g3 := (key (s₁ + a)).2
  have g4 := (hgrow (k ^ 2 * (m' * (s₁ + a)))
    (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (Nat.mul_ne_zero (by omega) (by omega))))).2
  have hm'f : 0 < m' ^ Module.finrank ℚ F := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hm'f
  calc Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} * s₁ ^ Module.finrank ℚ F * m' ^ Module.finrank ℚ F
      = Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} * (m' * s₁) ^ Module.finrank ℚ F := by ring
    _ ≤ Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} *
        (c₀ * Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((m' * s₁ : ℕ) : ℤ)) ⊤)) := Nat.mul_le_mul_left _ g1
    _ = c₀ * (Nat.card {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} *
        Module.finrank Ω (SecOnR X.A.hom (pw (pw (X.diag c) m) ((m' * s₁ : ℕ) : ℤ)) ⊤)) := by ring
    _ ≤ c₀ * (C₀ * (k ^ 2 * (m' * (s₁ + a))) ^ Module.finrank ℚ F) :=
        Nat.mul_le_mul_left _ ((g2.trans g3).trans g4)
    _ = c₀ * C₀ * k ^ (2 * Module.finrank ℚ F) * (s₁ + a) ^ Module.finrank ℚ F * m' ^ Module.finrank ℚ F := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring

end GlobalTheory.RealMultKernel
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SmallNorm

open Module

theorem exists_pow_between (N f : ℕ) (hN : 1 ≤ N) (hf : 1 ≤ f) :
    ∃ r : ℕ, 1 ≤ r ∧ N ≤ r ^ f ∧ r ^ f ≤ 2 ^ f * N := by
  classical
  have hex : ∃ r : ℕ, N ≤ r ^ f := ⟨N, Nat.le_self_pow (by omega) N⟩
  have hP : N ≤ (Nat.find hex) ^ f := Nat.find_spec hex
  have hr0 : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, zero_pow (by omega)] at hP; omega
    · exact h
  refine ⟨Nat.find hex, hr0, hP, ?_⟩
  rcases Nat.eq_or_lt_of_le hr0 with h | h
  · rw [← h, one_pow]
    calc 1 ≤ 2 ^ f := Nat.one_le_two_pow
      _ ≤ 2 ^ f * N := Nat.le_mul_of_pos_right _ hN
  · have hlt : (Nat.find hex - 1) ^ f < N :=
      not_le.mp (Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega))
    calc (Nat.find hex) ^ f ≤ (2 * (Nat.find hex - 1)) ^ f := Nat.pow_le_pow_left (by omega) f
      _ = 2 ^ f * (Nat.find hex - 1) ^ f := by rw [mul_pow]
      _ ≤ 2 ^ f * N := Nat.mul_le_mul_left _ hlt.le

theorem isCoprime_norm_of_eq {F : Type} [Field F] [NumberField F] (q : ℕ) (b y : 𝓞 F)
    (h : b = 1 + (q : 𝓞 F) * y) : IsCoprime (Algebra.norm ℤ b) (q : ℤ) := by
  classical
  have key : ((Algebra.norm ℤ b : ℤ) : ZMod q) = 1 := by
    rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis F), ← eq_intCast (Int.castRingHom (ZMod q)),
      RingHom.map_det, h, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]
    simp
  have hd : (q : ℤ) ∣ Algebra.norm ℤ b - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [key, sub_self]
  obtain ⟨m, hm⟩ := hd
  exact ⟨1, -m, by linarith⟩

theorem exists_small_coprime_norm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (q : ℕ), 1 ≤ q → ∃ C : ℕ,
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → IsCoprime I (Ideal.span {(q : 𝓞 F)}) →
      ∃ b ∈ I, b ≠ 0 ∧ IsCoprime (Algebra.norm ℤ b) (q : ℤ) ∧
        ∃ k : ℕ, IsTotPos (((k : F)) ^ 2 - (b : F) ^ 2) ∧ k ^ Module.finrank ℚ F ≤ C * Ideal.absNorm I := by
  intro F _ _ _ q hq
  classical
  have hf : 0 < finrank ℚ F := finrank_pos
  set D : ℝ := Real.sqrt |(discr F : ℝ)| with hD_def
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  set c₀ : ℝ := 3 * D ^ ((finrank ℚ F : ℝ)⁻¹) with hc₀_def
  have hc₀ : 0 ≤ c₀ := by positivity
  have habs : ∀ (τ : F →+* ℝ) (y : F), |τ y| = InfinitePlace.mk (Complex.ofRealHom.comp τ) y := by
    intro τ y
    rw [InfinitePlace.apply, RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]
  set C₂ : ℝ := ∑ i, ∑ w : InfinitePlace F, w (integralBasis F i) with hC₂_def
  have hC₂ : ∀ (τ : F →+* ℝ) i, |τ (integralBasis F i)| ≤ ∑ w : InfinitePlace F, w (integralBasis F i) := by
    intro τ i
    rw [habs]
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => w (integralBasis F i))
      (fun w _ => apply_nonneg w _) (Finset.mem_univ _)
  have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
  set K₀ : ℕ := ⌈(q : ℝ) * c₀ * (C₂ + 1)⌉₊ + 1 with hK₀_def
  refine ⟨K₀ ^ finrank ℚ F * 2 ^ finrank ℚ F, ?_⟩
  intro I hI hcop
  have hN : 1 ≤ Ideal.absNorm I := Nat.one_le_iff_ne_zero.2 (fun h => hI (Ideal.absNorm_eq_zero_iff.1 h))
  obtain ⟨r, hr1, hNr, hr2⟩ := exists_pow_between (Ideal.absNorm I) (finrank ℚ F) hN hf

  obtain ⟨a₀, ha₀I, ha₀0, ha₀⟩ := ReciprocityTheory.ChartRestriction.G.TB.Mink.exists_small_mem_ideal' F I hI
  have hsmall : ∀ τ : F →+* ℝ, |τ (a₀ : F)| ≤ c₀ * r := by
    intro τ
    have h1 := ha₀ (Complex.ofRealHom.comp τ)
    rw [RingHom.comp_apply, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs] at h1
    refine h1.le.trans ?_
    have hNr' : (Ideal.absNorm I : ℝ) ≤ (r : ℝ) ^ finrank ℚ F := by exact_mod_cast hNr
    calc 3 * ((Ideal.absNorm I : ℝ) * D) ^ ((finrank ℚ F : ℝ)⁻¹)
        ≤ 3 * (((r : ℝ) ^ finrank ℚ F) * D) ^ ((finrank ℚ F : ℝ)⁻¹) := by gcongr
      _ = c₀ * r := by
          rw [Real.mul_rpow (by positivity) hD, Real.pow_rpow_inv_natCast (by positivity) hf.ne', hc₀_def]
          ring

  rw [Ideal.isCoprime_iff_add, Ideal.one_eq_top, Ideal.eq_top_iff_one, Ideal.add_eq_sup, Submodule.mem_sup] at hcop
  obtain ⟨x, hxI, z, hz, hxz⟩ := hcop
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  have hq0 : (q : F) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  set b₀ : 𝓞 F := (q : 𝓞 F) * a₀ with hb₀_def
  have hb₀F : (b₀ : F) = (q : F) * (a₀ : F) := by simp [hb₀_def]
  have ha₀F : (a₀ : F) ≠ 0 := by simpa using ha₀0
  have hb₀ : (b₀ : F) ≠ 0 := by rw [hb₀F]; exact mul_ne_zero hq0 ha₀F
  have hb₀I : b₀ ∈ I := Ideal.mul_mem_left _ _ ha₀I

  set zz : F := (x : F) / (b₀ : F) with hzz
  set c := (integralBasis F).repr zz with hc
  set t : 𝓞 F := ∑ i, ⌊c i⌋ • RingOfIntegers.basis F i with ht_def
  have hdec : zz - (t : F) = ∑ i, ((Int.fract (c i) : ℚ) : F) * integralBasis F i := by
    have h1 : zz = ∑ i, ((c i : ℚ) : F) * integralBasis F i := by
      conv_lhs => rw [← (integralBasis F).sum_repr zz]
      simp [Rat.smul_def, hc]
    have h2 : (t : F) = ∑ i, (((⌊c i⌋ : ℤ) : ℚ) : F) * integralBasis F i := by
      simp [ht_def, integralBasis_apply, zsmul_eq_mul]
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Int.fract, ← sub_mul]; push_cast; ring
  have hfr : ∀ τ : F →+* ℝ, |τ (zz - (t : F))| ≤ C₂ := by
    intro τ
    rw [hdec, map_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [map_mul, map_ratCast, abs_mul]
    have e1 : |((Int.fract (c i) : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by exact_mod_cast Int.fract_nonneg _)]
      exact_mod_cast (Int.fract_lt_one _).le
    calc |((Int.fract (c i) : ℚ) : ℝ)| * |τ (integralBasis F i)| ≤ 1 * |τ (integralBasis F i)| := by
          gcongr
      _ ≤ _ := by rw [_root_.one_mul]; exact hC₂ τ i

  obtain ⟨s, hs0, hs⟩ : ∃ s : 𝓞 F, x - b₀ * s ≠ 0 ∧ ∀ τ : F →+* ℝ, |τ (zz - (s : F))| ≤ C₂ + 1 := by
    by_cases h0 : x - b₀ * t = 0
    · refine ⟨t + 1, ?_, fun τ => ?_⟩
      · intro h; apply ha₀0
        have : b₀ = 0 := by linear_combination h0 - h
        rw [hb₀_def] at this
        rcases mul_eq_zero.1 this with h' | h'
        · exact absurd (by exact_mod_cast h' : (q : F) = 0) hq0
        · exact h'
      · have : τ (zz - ((t + 1 : 𝓞 F) : F)) = τ (zz - (t : F)) - 1 := by
          push_cast; simp only [map_sub, map_add, map_one]; ring
        rw [this]
        calc |τ (zz - (t : F)) - 1| ≤ |τ (zz - (t : F))| + |(1 : ℝ)| := abs_sub _ _
          _ ≤ C₂ + 1 := by rw [abs_one]; linarith [hfr τ]
    · exact ⟨t, h0, fun τ => (hfr τ).trans (by linarith)⟩
  set b : 𝓞 F := x - b₀ * s with hb_def
  have hbI : b ∈ I := I.sub_mem hxI (Ideal.mul_mem_right _ _ hb₀I)
  have hbq : b = 1 + (q : 𝓞 F) * (-u - a₀ * s) := by
    rw [hb_def, hb₀_def]; linear_combination hxz
  have hbF : (b : F) = (b₀ : F) * (zz - (s : F)) := by
    rw [hzz, hb_def]; push_cast; field_simp
  have hbnd : ∀ τ : F →+* ℝ, |τ (b : F)| < (K₀ * r : ℕ) := by
    intro τ
    rw [hbF, map_mul, abs_mul, hb₀F, map_mul, map_natCast, abs_mul, Nat.abs_cast]
    have hr : (0 : ℝ) < r := by exact_mod_cast hr1
    have hK : (q : ℝ) * c₀ * (C₂ + 1) < K₀ := by
      rw [hK₀_def]; push_cast; linarith [Nat.le_ceil ((q : ℝ) * c₀ * (C₂ + 1))]
    calc (q : ℝ) * |τ (a₀ : F)| * |τ (zz - (s : F))| ≤ (q : ℝ) * (c₀ * r) * (C₂ + 1) := by
          gcongr
          · exact hsmall τ
          · exact hs τ
      _ = ((q : ℝ) * c₀ * (C₂ + 1)) * r := by ring
      _ < K₀ * r := by gcongr
      _ = ((K₀ * r : ℕ) : ℝ) := by push_cast; ring
  refine ⟨b, hbI, hs0, isCoprime_norm_of_eq q b _ hbq, K₀ * r, ?_, ?_⟩
  · intro τ
    have h := abs_lt.1 (hbnd τ)
    rw [map_sub, map_pow, map_pow, map_natCast]
    nlinarith [h.1, h.2]
  · rw [mul_pow, _root_.mul_assoc]
    exact Nat.mul_le_mul_left _ hr2

end GlobalTheory.SmallNorm
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult

namespace TorsRankTwo

open LevFlat

@[reducible] def addModule {M O : Type} [CommGroup M] [CommRing O] {ρ : O → M →* M} (h : IsAct ρ) :
    Module O (Additive M) where
  smul a x := Additive.ofMul (ρ a x.toMul)
  one_smul x := h.one x.toMul
  mul_smul a b x := by
    show ρ (a * b) x.toMul = ρ a (ρ b x.toMul)
    rw [mul_comm, h.mul]
  smul_zero a := map_one (ρ a)
  smul_add a x y := map_mul (ρ a) x.toMul y.toMul
  add_smul a b x := h.add a b x.toMul
  zero_smul x := h.zero x.toMul

theorem exists_charExp (F : Type) [Field F] [NumberField F] (N : ℕ) (Ω : Type) [Field Ω] (hN : (N : Ω) ≠ 0) :
    ∃ q : ℕ, 1 ≤ q ∧ (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 → IsCoprime 𝔭 (Ideal.span {(q : 𝓞 F)})) ∧
      ∀ b : 𝓞 F, b ≠ 0 → IsCoprime (Algebra.norm ℤ b) (q : ℤ) → ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpp | rfl
  · refine ⟨p, hpp.one_le, fun 𝔭 h𝔭 hN𝔭 => ?_, fun b _ hb h0 => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have hp𝔭 : (p : 𝓞 F) ∈ 𝔭 := by
        rw [h𝔭.eq_of_le hne le_sup_left]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      have hc : Nat.Coprime p N := hpp.coprime_iff_not_dvd.2 fun h => hN ((CharP.cast_eq_zero_iff Ω p N).2 h)
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hc).map (Int.castRingHom (𝓞 F))
      simp only [map_natCast] at huv
      exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 (huv ▸ 𝔭.add_mem (𝔭.mul_mem_left u hp𝔭) (𝔭.mul_mem_left v hN𝔭)))
    · obtain ⟨u, v, huv⟩ := hb.map (Int.castRingHom Ω)
      rw [map_natCast, CharP.cast_eq_zero, eq_intCast, h0] at huv
      simp at huv
  · haveI := CharP.charP_to_charZero Ω
    refine ⟨1, le_rfl, fun 𝔭 _ _ => ?_, fun b hb _ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq, Nat.cast_one, Ideal.span_singleton_one, sup_top_eq]
    · exact Int.cast_ne_zero.2 (Algebra.norm_ne_zero_iff.2 hb)

theorem exists_ptEquiv {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {S S' : Scheme.{0}} {X : Obj F 𝔠 S}
    {X' : Obj F 𝔠 S'} {t : S' ⟶ S} {φ : X'.A.left ⟶ X.A.left} (h : X'.IsPullBy X t φ) :
    ∃ e : (𝟙_ (Over S') ⟶ X'.A) ≃* (Over.mk t ⟶ X.A), ∀ x a, e (x ≫ X'.rm.act a) = e x ≫ X.rm.act a := by
  have key : ∀ t' : S' ⟶ S, (𝟙_ (Over S')).hom ≫ t = t' →
      ∃ e : (𝟙_ (Over S') ⟶ X'.A) ≃* (Over.mk t' ⟶ X.A), ∀ x a, e (x ≫ X'.rm.act a) = e x ≫ X.rm.act a := by
    rintro _ rfl
    obtain ⟨e, he⟩ := ptEquiv h.grp (𝟙_ (Over S'))
    refine ⟨e, fun x a => Over.OverMorphism.ext ?_⟩
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, h.act]
  exact key t (Category.id_comp t)

end TorsRankTwo

open LevFlat TorsRankTwo

theorem torsion_free_rank_two :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) := by
  intro F _ _ _ 𝔠 S X N Ω _ _ t hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN Nat.cast_zero
  obtain ⟨X', φ, hφ⟩ := X.exists_isPullBy t
  obtain ⟨e, he⟩ := exists_ptEquiv hφ
  letI : Module (𝓞 F) (Additive (Over.mk t ⟶ X.A)) := addModule (isAct_ptAct X (Over.mk t))
  obtain ⟨q, hq, hq𝔭, hqb⟩ := exists_charExp F N Ω hN
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.RealMultKernel.card_ker_act_le F 𝔠 Ω X'
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.SmallNorm.exists_small_coprime_norm F q hq
  obtain ⟨p, h1, h2, h3⟩ := GlobalTheory.RankTwoTorsion.rank_two_torsion F (Additive (Over.mk t ⟶ X.A)) N
    (Nat.one_le_iff_ne_zero.2 hN0)
    (fun j => by
      rw [← GlobalTheory.abMulN_holds Ω X'.A _ (N ^ j) X'.ab X'.dim (by rw [Nat.cast_pow]; exact pow_ne_zero j hN)]
      refine Nat.card_congr (Equiv.subtypeEquiv (Additive.toMul.trans e.symm.toEquiv) fun x => ?_)
      show x.toMul ^ (N ^ j) = 1 ↔ e.symm x.toMul ^ (N ^ j) = 1
      rw [← map_pow e.symm, e.symm.map_eq_one_iff])
    (fun 𝔭 h𝔭 hN𝔭 => ⟨C₀ * C₁ ^ 2, fun n => by
      have hI : 𝔭 ^ n ≠ ⊥ := fun h0 => by
        have := Ideal.pow_mem_pow hN𝔭 n
        rw [h0, Ideal.mem_bot] at this
        exact pow_ne_zero n (Nat.cast_ne_zero.2 hN0) this
      obtain ⟨b, hbI, hb0, hbq, k, hk, hkf⟩ := hC₁ (𝔭 ^ n) hI (hq𝔭 𝔭 h𝔭 hN𝔭).pow_left
      obtain ⟨hfin, hle⟩ := hC₀ b k (hqb b hb0 hbq) hk
      let f : {x : Additive (Over.mk t ⟶ X.A) // ∀ a ∈ 𝔭 ^ n, a • x = 0} →
          {y : 𝟙_ (Over (Sp Ω)) ⟶ X'.A // y ≫ X'.rm.act b = 1} := fun x =>
        ⟨e.symm x.1.toMul, e.injective (by
          rw [he, e.apply_symm_apply, map_one]
          exact x.2 b hbI)⟩
      have hf : Function.Injective f := fun x y hxy =>
        Subtype.ext (Additive.toMul.injective (e.symm.injective (congrArg Subtype.val hxy)))
      refine (Nat.card_le_card_of_injective f hf).trans (hle.trans ?_)
      rw [map_pow] at hkf
      calc C₀ * k ^ (2 * Module.finrank ℚ F) = C₀ * (k ^ Module.finrank ℚ F) ^ 2 := by ring
        _ ≤ C₀ * (C₁ * Ideal.absNorm 𝔭 ^ n) ^ 2 := by gcongr
        _ = C₀ * C₁ ^ 2 * Ideal.absNorm 𝔭 ^ (2 * n) := by ring⟩)
  exact ⟨fun i => (p i).toMul, h1, h2, fun y hy => h3 (Additive.ofMul y) hy⟩

end GlobalTheory.RealMult
end
end
