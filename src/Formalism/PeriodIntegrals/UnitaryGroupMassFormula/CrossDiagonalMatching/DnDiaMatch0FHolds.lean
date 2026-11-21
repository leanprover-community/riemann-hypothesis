import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Common
import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.NaturalTranslateAdelicFunction
import Formalism.LocalToGlobal.GroupLattices.Joint0

section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dnk_tld (T : Forms0 D u) (c : (D.mem u).C.cls 0) (y : Fin (D.R.N 0) → D.host.E)
    (hy : y ∈ Ld D u 0 (Nat.zero_le _) c) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • y ∈ clsCrd D u 0 (Nat.zero_le _) c := by
  rw [Nat.cast_smul_eq_nsmul]
  have hLd := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0.dual_class_lattice_eq_global T.cls0 c
  have hfin := tld_isLat (u := u) 0 (Nat.zero_le _) c
  have hone := Formalism.L2.GlobalTheoryTheory.Comp.glob_one (F := D.host.F) hfin
  have hdl : ∀ x ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb,
      ((D.mem u).A.T : ℕ) • x ∈ T.cls0.lev.Lb := by
    intro x hx
    unfold Formalism.L2.GlobalTheoryTheory.Comp.dl at hx
    induction hx using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul D.host.E]; exact T.cls0.lev.Lb_dual x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ ihx ihy => rw [smul_add]; exact add_mem ihx ihy
    | smul a x _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih
  have hkey : ∀ w ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (Formalism.L2.GlobalTheoryTheory.Comp.dl (sigD D) (gramN D 0 (Nat.zero_le _)) T.cls0.lev.Lb),
      ((D.mem u).A.T : ℕ) • w ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) T.cls0.lev.Lb := by
    intro w hw
    unfold latS at hw ⊢
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      apply Submodule.subset_span
      refine ⟨_, hdl x hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, map_nsmul]
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ ihx ihy => rw [smul_add]; exact add_mem ihx ihy
    | smul a x _ ih => rw [smul_comm]; exact Submodule.smul_mem _ a ih
  have hmem : ∀ (g : GL (Fin (D.R.N 0)) (TensorProduct D.host.F D.host.E (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
      (Λ : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (x : Fin (D.R.N 0) → D.host.E),
      x ∈ Formalism.UG.CS.globLat g Λ ↔ ((g⁻¹ : GL _ _) : Matrix _ _ _) *ᵥ
        (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) Λ :=
    fun _ _ _ => Iff.rfl
  rw [hLd, hmem] at hy
  rw [← hone, hmem, inv_one, Units.val_one, Matrix.one_mulVec, T.cls0.y_lat c]
  have e : (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ((((D.mem u).A.T : ℕ) • y) i)) =
      ((D.mem u).A.T : ℕ) • (fun i => inclE (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (y i)) := by
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  rw [e, Matrix.mulVec_smul]
  exact hkey _ hy

theorem dnk_lk_le (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    Lk T.atT 0 (Nat.zero_le _) v c ≤ Ld D u 0 (Nat.zero_le _) c := sup_le (cls_le_ld T c) Submodule.smul_le_right

set_option maxHeartbeats 2000000 in

theorem dnk_lk_locP (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Lk T.atT 0 (Nat.zero_le _) v c) ≤
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
  intro x hx
  have hx' : ∃ s ∈ (T.atT.Pv v).primeCompl, s • x ∈ Lk T.atT 0 (Nat.zero_le _) v c := hx
  obtain ⟨s, hs, hsx⟩ := hx'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsx
  obtain ⟨t, ht, y, hy, hty⟩ := exists_smul_eq_smul_of_mem_ideal_smul T.atT v (Ld D u 0 (Nat.zero_le _) c) b hb
  show ∃ r ∈ (T.atT.Pv v).primeCompl, r • x ∈ clsCrd D u 0 (Nat.zero_le _) c
  refine ⟨t * s, Submonoid.mul_mem _ (Ideal.mem_primeCompl_iff.mpr ht) hs, ?_⟩
  rw [mul_smul, ← hab, smul_add, hty]
  exact Submodule.add_mem _ (Submodule.smul_mem _ t ha) (dnk_tld T c y hy)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem dnk_char (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (γ : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (y : Fin (D.R.N 0) → D.host.E) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔
      ∃ s : 𝓞 D.host.E, s ∉ T.atT.Pv v ∧ ∃ h : s • y ∈ Lk T.atT 0 (Nat.zero_le _) v c,
        g (T.lv0.prk v c ⟨_, h⟩) = 0 := by
  have memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L := fun _ _ => Iff.rfl
  have memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z := fun _ _ _ => Iff.rfl
  have hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x) :=
    fun M t x => Matrix.mulVec_smul M t x
  have hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl →
      a * b ∈ (T.atT.Pv v).primeCompl := fun ha hb => Submonoid.mul_mem _ ha hb
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := (memP _ _).mp hy
    obtain ⟨x, hx, hxy⟩ := (memM _ _ _).mp hsy
    have hxd : x ∈ Ld D u 0 (Nat.zero_le _) c1 := dnk_lk_le T v c1 hx
    have h1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
      rw [← hl]
      exact (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hxd, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp h1
    have htx' : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x) ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [hsm]; exact Submodule.mem_sup_left htx
    have hfx : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨t • x, Submodule.smul_mem _ t hxd⟩) = 0 :=
      (T.lv0.fv_ker v c1 _).mpr (Submodule.smul_mem _ t hx)
    have hmem : (t * s) • y ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [mul_smul, ← hxy, ← hsm]; exact htx'
    refine ⟨t * s, Ideal.mem_primeCompl_iff.mp (hPc ht hs), hmem, ?_⟩
    have e : (⟨(t * s) • y, hmem⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = ⟨_, htx'⟩ := by
      apply Subtype.ext
      show (t * s) • y = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (t • x)
      rw [mul_smul, ← hxy, hsm]
    rw [e]
    exact (hfun ⟨t • x, Submodule.smul_mem _ t hxd⟩ htx').symm.trans hfx
  · rintro ⟨s, hs, hsy, hg⟩
    have h1 : s • y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) :=
      dnk_lk_locP T v c ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hsy⟩)
    rw [← hl] at h1
    obtain ⟨t, ht, htm⟩ := (memP _ _).mp h1
    obtain ⟨x, hx, hxe⟩ := (memM _ _ _).mp htm
    have hxk : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Lk T.atT 0 (Nat.zero_le _) v c := by
      rw [hxe]; exact Submodule.smul_mem _ t hsy
    have hf : (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨x, hx⟩) = g (T.lv0.prk v c ⟨_, hxk⟩) := hfun ⟨x, hx⟩ hxk
    have e : (⟨_, hxk⟩ : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) = t • ⟨s • y, hsy⟩ := Subtype.ext hxe
    rw [e, T.lv0.prk_smul, map_smul, hg, smul_zero] at hf
    have hxk1 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c1 := (T.lv0.fv_ker v c1 ⟨x, hx⟩).mp hf
    exact (memP _ _).mpr ⟨t * s, hPc ht (Ideal.mem_primeCompl_iff.mpr hs),
      (memM _ _ _).mpr ⟨x, hxk1, by rw [hxe, mul_smul]⟩⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem dnk_latP (T : Forms0 D u) (v : (D.mem u).A.vT) (c c1 c2 : (D.mem u).C.cls 0)
    (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (γ γ' : GL (Fin (D.R.N 0)) D.host.E)
    (hl : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hx : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 x) = g (T.lv0.prk v c ⟨_, hx⟩))
    (hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hfun' : ∀ (x : ↥(Ld D u 0 (Nat.zero_le _) c2)) (hx : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c2 (T.lv0.pr v c2 x) = g (T.lv0.prk v c ⟨_, hx⟩)) :
    Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
      (clsCrd D u 0 (Nat.zero_le _) c2)) =
      Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c1) := by
  have memP : ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) L ↔ ∃ s ∈ (T.atT.Pv v).primeCompl, s • z ∈ L := fun _ _ => Iff.rfl
  have memM : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E)) (z : Fin (D.R.N 0) → D.host.E),
      z ∈ mulLat M L ↔ ∃ x ∈ L, M *ᵥ x = z := fun _ _ _ => Iff.rfl
  have hsm : ∀ (M : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (t : 𝓞 D.host.E) (x : Fin (D.R.N 0) → D.host.E), M *ᵥ (t • x) = t • (M *ᵥ x) :=
    fun M t x => Matrix.mulVec_smul M t x
  have hPc : ∀ {a b : 𝓞 D.host.E}, a ∈ (T.atT.Pv v).primeCompl → b ∈ (T.atT.Pv v).primeCompl →
      a * b ∈ (T.atT.Pv v).primeCompl := fun ha hb => Submonoid.mul_mem _ ha hb
  have hloc : ∀ (c' : (D.mem u).C.cls 0) (w : Fin (D.R.N 0) → D.host.E), w ∈ Lk T.atT 0 (Nat.zero_le _) v c' →
      ∃ r ∈ (T.atT.Pv v).primeCompl, r • w ∈ clsCrd D u 0 (Nat.zero_le _) c' := fun c' w hw =>
    (memP _ _).mp (dnk_lk_locP T v c' ((memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hw⟩))
  have hA : ∀ y, y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) ↔
      y ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) := fun y =>
    (dnk_char T v c c1 g γ hl hfun y).trans (dnk_char T v c c2 g γ' hl' hfun' y).symm
  have hcomp : ∀ x : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ * γ' : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x) :=
    fun x => by rw [Units.val_mul, Matrix.mulVec_mulVec]
  have hinv : ∀ w : Fin (D.R.N 0) → D.host.E, ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hinv' : ∀ w : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinj : ∀ a b : Fin (D.R.N 0) → D.host.E, (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ a = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ b → a = b := fun a b h =>
    (hinv a).symm.trans ((congrArg (fun w => ((γ⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w) h).trans (hinv b))
  ext z
  constructor
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (memP _ _).mp hz
    obtain ⟨x, hx, hxz⟩ := (memM _ _ _).mp hsz
    have hx2 : x ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := Submodule.mem_sup_left hx
    have hA2 : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c2)) :=
      (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨x, hx2, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp ((hA _).mpr hA2)
    obtain ⟨w, hw, hwx⟩ := (memM _ _ _).mp htx
    have hx' : (γ' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ x = (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) := by rw [← hxz, hcomp, hinv']
    have hwz : w = (t * s) • z := by
      apply hinj
      rw [hwx, hx', mul_smul, hsm _ t (s • z)]
    obtain ⟨r, hr, hrw⟩ := hloc c1 w hw
    exact (memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), by rw [mul_smul, ← hwz]; exact hrw⟩
  · intro hz
    obtain ⟨s, hs, hsz⟩ := (memP _ _).mp hz
    have hk1 : s • z ∈ Lk T.atT 0 (Nat.zero_le _) v c1 := Submodule.mem_sup_left hsz
    have hA1 : (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • z) ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c1)) :=
      (memP _ _).mpr ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact (memM _ _ _).mpr ⟨_, hk1, rfl⟩⟩
    obtain ⟨t, ht, htx⟩ := (memP _ _).mp ((hA _).mp hA1)
    obtain ⟨w, hw, hwx⟩ := (memM _ _ _).mp htx
    obtain ⟨r, hr, hrw⟩ := hloc c2 w hw
    refine (memP _ _).mpr ⟨r * (t * s), hPc hr (hPc ht hs), (memM _ _ _).mpr ⟨r • w, hrw, ?_⟩⟩
    simp only [hcomp, hsm, hwx, hinv, mul_smul]

end CrossDiaZero

end
end

section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

def dualSigma {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (φ : W ≃ₗ[K] V) (tv : V) (tw : W) (h : φ tw = tv) :
    {x : Module.Dual K V // x tv = 1} ≃ {y : Module.Dual K W // y tw = 1} where
  toFun x := ⟨x.1 ∘ₗ φ.toLinearMap, by rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h]; exact x.2⟩
  invFun y := ⟨y.1 ∘ₗ φ.symm.toLinearMap, by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← h, LinearEquiv.symm_apply_apply]; exact y.2⟩
  left_inv x := Subtype.ext (LinearMap.ext fun w => by simp)
  right_inv y := Subtype.ext (LinearMap.ext fun w => by simp)

theorem dualSigma_apply {K V W : Type} [CommRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (φ : W ≃ₗ[K] V) (tv : V) (tw : W) (h : φ tw = tv) (x : {x : Module.Dual K V // x tv = 1}) (w : W) :
    (dualSigma φ tv tw h x).1 w = x.1 (φ w) := rfl

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 2000000 in

theorem dni_lk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c') :
    mulLat g (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c' := by
  show mulLat g (clsCrd D u 0 (Nat.zero_le _) c ⊔ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c) =
    clsCrd D u 0 (Nat.zero_le _) c' ⊔ T.atT.Pv v • Ld D u 0 (Nat.zero_le _) c'
  unfold mulLat at hL hLd ⊢
  rw [Submodule.map_sup, Submodule.map_smul'', hL, hLd]

theorem dni_mem_of {E : Type} [Field E] [NumberField E] {n : ℕ} (g : Matrix (Fin n) (Fin n) E)
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : mulLat g M = M') {z : Fin n → E} (hz : z ∈ M) : g *ᵥ z ∈ M' := by
  rw [← h]
  exact Submodule.mem_map_of_mem hz

set_option maxHeartbeats 2000000 in
theorem dni_mem (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    {z : Fin (D.R.N 0) → D.host.E} (hz : z ∈ Lk T.atT 0 (Nat.zero_le _) v c) :
    g *ᵥ z ∈ Lk T.atT 0 (Nat.zero_le _) v c' :=
  dni_mem_of g (dni_lk T v c c' g hL hLd) hz

set_option maxHeartbeats 2000000 in
theorem dni_mem_ker (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    {z : Fin (D.R.N 0) → D.host.E} (hz : z ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c) :
    g *ᵥ z ∈ T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c' := by
  have h := dni_lk T v c c' g hL hLd
  have h2 : mulLat g (T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c) =
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c' := by
    unfold mulLat at h ⊢
    rw [Submodule.map_smul'', h]
  exact dni_mem_of g h2 hz

def dniFun (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (w : (D.fm u).lk 0 v c) : (D.fm u).lk 0 v c' :=
  T.lv0.prk v c' ⟨g *ᵥ (Function.surjInv (T.lv0.prk_surj v c) w).1,
    dni_mem T v c c' g hL hLd (Function.surjInv (T.lv0.prk_surj v c) w).2⟩

set_option maxHeartbeats 2000000 in
theorem dniFun_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniFun T v c c' g hL hLd (T.lv0.prk v c z) = T.lv0.prk v c' ⟨g *ᵥ z.1, dni_mem T v c c' g hL hLd z.2⟩ := by
  have hs := Function.surjInv_eq (T.lv0.prk_surj v c) (T.lv0.prk v c z)
  have hd : (Function.surjInv (T.lv0.prk_surj v c) (T.lv0.prk v c z) - z).1 ∈
      T.atT.Pv v • Lk T.atT 0 (Nat.zero_le _) v c := by
    rw [← T.lv0.prk_ker, map_sub, hs, sub_self]
  have hg := dni_mem_ker T v c c' g hL hLd hd
  unfold dniFun
  rw [← sub_eq_zero, ← map_sub, T.lv0.prk_ker]
  simpa [Matrix.mulVec_sub] using hg

set_option maxHeartbeats 2000000 in

def dniLin (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c') :
    (D.fm u).lk 0 v c →ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c' where
  toFun := dniFun T v c c' g hL hLd
  map_add' w1 w2 := by
    obtain ⟨z1, rfl⟩ := T.lv0.prk_surj v c w1
    obtain ⟨z2, rfl⟩ := T.lv0.prk_surj v c w2
    rw [← map_add, dniFun_prk, dniFun_prk, dniFun_prk, ← map_add]
    congr 1
    apply Subtype.ext
    show g *ᵥ (z1.1 + z2.1) = g *ᵥ z1.1 + g *ᵥ z2.1
    exact Matrix.mulVec_add _ _ _
  map_smul' r w := by
    obtain ⟨a, rfl⟩ := T.atT.res_surj v r
    obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
    rw [RingHom.id_apply, ← T.lv0.prk_smul, dniFun_prk, dniFun_prk, ← T.lv0.prk_smul]
    congr 1
    apply Subtype.ext
    show g *ᵥ (a • z.1) = a • (g *ᵥ z.1)
    exact Matrix.mulVec_smul _ _ _

theorem dniLin_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0)
    (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat g (clsCrd D u 0 (Nat.zero_le _) c) = clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat g (Ld D u 0 (Nat.zero_le _) c) = Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniLin T v c c' g hL hLd (T.lv0.prk v c z) = T.lv0.prk v c' ⟨g *ᵥ z.1, dni_mem T v c c' g hL hLd z.2⟩ :=
  dniFun_prk T v c c' g hL hLd z

theorem dni_inv_eq {E : Type} [Field E] [NumberField E] {n : ℕ} (g : GL (Fin n) E)
    {M M' : Submodule (𝓞 E) (Fin n → E)} (h : mulLat (g : Matrix (Fin n) (Fin n) E) M = M') :
    mulLat ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) M' = M := by
  have hid : ((Matrix.mulVecLin ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)).comp
      ((Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      LinearMap.id_apply]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← h]
  unfold mulLat
  rw [← Submodule.map_comp, hid, Submodule.map_id]

set_option maxHeartbeats 2000000 in

def dniEquiv (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c') :
    (D.fm u).lk 0 v c ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk 0 v c' :=
  LinearEquiv.ofLinear (dniLin T v c c' _ hL hLd) (dniLin T v c' c _ (dni_inv_eq g hL) (dni_inv_eq g hLd))
    (LinearMap.ext fun w => by
      obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c' w
      rw [LinearMap.comp_apply, dniLin_prk, dniLin_prk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      show (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        (((g⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])
    (LinearMap.ext fun w => by
      obtain ⟨z, rfl⟩ := T.lv0.prk_surj v c w
      rw [LinearMap.comp_apply, dniLin_prk, dniLin_prk, LinearMap.id_apply]
      congr 1
      apply Subtype.ext
      show ((g⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ
        ((g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec])

theorem dniEquiv_prk (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Lk T.atT 0 (Nat.zero_le _) v c)) :
    dniEquiv T v c c' g hL hLd (T.lv0.prk v c z) =
      T.lv0.prk v c' ⟨(g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1, dni_mem T v c c' _ hL hLd z.2⟩ :=
  dniLin_prk T v c c' _ hL hLd z

set_option maxHeartbeats 2000000 in

theorem dniEquiv_te (T : Forms0 D u) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls 0) (g : GL (Fin (D.R.N 0)) D.host.E)
    (hL : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c) =
      clsCrd D u 0 (Nat.zero_le _) c')
    (hLd : mulLat (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c) =
      Ld D u 0 (Nat.zero_le _) c')
    (z : ↥(Ld D u 0 (Nat.zero_le _) c)) (hz : (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1)
    (hgz : (g : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) c')
    (hz' : (D.fm u).fv 0 v c' (T.lv0.pr v c' ⟨_, hgz⟩) = 1) :
    dniEquiv T v c c' g hL hLd ((D.fm u).te 0 v c) = (D.fm u).te 0 v c' := by
  have e1 := T.lv0.te v c z hz
    (Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u T.atT v) z.2))
  have e2 := T.lv0.te v c' ⟨_, hgz⟩ hz'
    (Submodule.mem_sup_right (Submodule.smul_mem_smul (bwA_T_mem_Pv D u T.atT v) hgz))
  rw [← e1, ← e2, dniEquiv_prk]
  congr 1
  apply Subtype.ext
  simp only [Matrix.mulVec_smul]

theorem dni_exists_one (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) :
    ∃ z : ↥(Ld D u 0 (Nat.zero_le _) c), (D.fm u).fv 0 v c (T.lv0.pr v c z) = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, (D.fm u).fv 0 v c w ≠ 0 := by
    by_contra h
    push_neg at h
    exact (D.fm u).fv_ne 0 v c (LinearMap.ext h)
  obtain ⟨z, hz⟩ := T.lv0.pr_surj v c (((D.fm u).fv 0 v c w)⁻¹ • w)
  refine ⟨z, ?_⟩
  rw [hz, map_smul, smul_eq_mul, inv_mul_cancel₀ hw]

end CrossDiaZero

end
end

section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.MainNotions.RT Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

def UpMatchAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), UpDiaMatch0F T

def DnMatchAll : Prop := ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), DnDiaMatch0F T



end CrossDiaZero

end
end

section
noncomputable section

namespace CrossDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix

variable {D : D7} {u : D.what₂.Word}

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dn_match_one (T : Forms0 D u) (v v' : (D.mem u).A.vT) (hvv : v ≠ v') (k : ℤ) (δ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hδ : IsDia T.cls0.lev (T.atT.eV v').1 (T.atT.eV v').2 k δ) (c c2 c1 c3 : (D.mem u).C.cls 0)
    (γd : GL (Fin (D.R.N 0)) D.host.E) (hγd : γd ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (κd : T.cls0.lev.U)
    (hrel : (T.cls0.y c).1 * δ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γd * (T.cls0.y c2).1 * κd.1)
    (hLc : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c2) = clsCrd D u 0 (Nat.zero_le _) c)
    (hLd : mulLat (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c2) = Ld D u 0 (Nat.zero_le _) c)
    (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c)) (x2 : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c2))
    (hxy : ∀ w, x2 w = x (dniEquiv T v c2 c γd hLc hLd w))
    (γ γ2 : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _))) (η η2 : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ κ2 : T.cls0.lev.U)
    (hs1 : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η.1 = 1)
    (hs2 : ∀ w, w ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) w) η2.1 = 1)
    (h1 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 * (T.cls0.y c1).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (h2 : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ2.1 * (T.cls0.y c3).1 = (T.cls0.y c2).1 * η2.1 * κ2.1)
    (hl1 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ.1.1 (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c))
    (hl2 : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat γ2.1.1 (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c2))
    (hf1 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c1)) (hw : γ.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c1 (T.lv0.pr v c1 w) = x (T.lv0.prk v c ⟨_, hw⟩))
    (hf2 : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x2 (T.lv0.prk v c2 ⟨_, hw⟩)) :
    η2.1⁻¹ * κd.1 * η.1 ∈ T.cls0.lev.U := by
  classical
  have hne : (T.atT.eV v).1 ≠ (T.atT.eV v').1 := fun e => hvv (T.atT.eV.injective (Subtype.ext e))
  have hδv : bc (prV (E := D.host.E) (T.atT.eV v).1) δ.1 = 1 := hδ.1 _ hne
  set g' : GL (Fin (D.R.N 0)) D.host.E := γd * γ2.1 with hg'
  have hl' : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c3)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
    rw [hg', Units.val_mul]
    exact rlv_chainP _ _ _ (by rw [hLc]) hl2
  have hLkinv : mulLat ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Lk T.atT 0 (Nat.zero_le _) v c) = Lk T.atT 0 (Nat.zero_le _) v c2 :=
    dni_inv_eq γd (dni_lk T v c2 c _ hLc hLd)
  have hf' : ∀ (w : ↥(Ld D u 0 (Nat.zero_le _) c3)) (hw : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c),
      (D.fm u).fv 0 v c3 (T.lv0.pr v c3 w) = x (T.lv0.prk v c ⟨_, hw⟩) := by
    intro w hw
    have e1 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1) = γ2.1.1 *ᵥ w.1 := by
      rw [hg', Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    have hw2 : γ2.1.1 *ᵥ w.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c2 := by
      rw [← e1]; exact dni_mem_of _ hLkinv hw
    rw [hf2 w hw2, hxy, dniEquiv_prk]
    refine congrArg x (congrArg (T.lv0.prk v c) (Subtype.ext ?_))
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (γ2.1.1 *ᵥ w.1) = (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w.1
    rw [hg', Units.val_mul, Matrix.mulVec_mulVec]
  have hPc := dnk_latP T v c c1 c3 x γ.1 g' hl1 hf1 hl' hf'
  set Γ : GL (Fin (D.R.N 0)) D.host.E := γ2.1⁻¹ * γd⁻¹ * γ.1 with hΓdef
  have hPΓ : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (clsCrd D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c3) := by
    have e2 : (γ.1⁻¹ * g')⁻¹ = Γ := by rw [hg', hΓdef]; group
    have := localization_inv_smul_eq _ (γ.1⁻¹ * g') hPc
    rwa [e2] at this
  have hPdΓ : Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) = Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (Ld D u 0 (Nat.zero_le _) c3) := by
    have e3 : g'⁻¹ * γ.1 = Γ := by rw [hg', hΓdef]; group
    have := localization_smul_cancel _ g' γ.1 (hl1.trans hl'.symm)
    rwa [e3] at this
  have hΓU : Γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) := mul_mem (mul_mem (inv_mem γ2.2) (inv_mem hγd)) γ.2
  have hUΓ := matching_unitary_eq T.cls0 c c1 c2 c3 γ.1 γ2.1 γd η η2 δ κ κ2 κd h1 h2 hrel
  have hQd : Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (mulLat (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) (Ld D u 0 (Nat.zero_le _) c1)) =
      Formalism.HermitianLatticesTheory.localization₂ (rlvQ T.atT v) (Ld D u 0 (Nat.zero_le _) c3) :=
    local_dual_Q_eq_of_P T.atT v c3 c1 Γ hΓU hPΓ
  have eΓ : ∀ z, (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) = γ.1.1 *ᵥ z := by
    intro z
    have e4 : g' * Γ = γ.1 := by rw [hg', hΓdef]; group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e4]
  have hF : ∀ z (hz : z ∈ Ld D u 0 (Nat.zero_le _) c1), ∃ a : 𝓞 D.host.F, a ∉ (T.atT.eV v).1.asIdeal ∧
      ∃ h : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3,
        (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, h⟩) =
          (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨(algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) • z,
            Submodule.smul_mem _ _ hz⟩) := by
    intro z hz
    obtain ⟨b, hbP, hbQ, hb⟩ := rlv_two (T.atT.Pv v) (rlvQ T.atT v) hPdΓ.le hQd.le
      (x := (Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ⟨z, hz, rfl⟩
    obtain ⟨r, hr, b', hb'⟩ := rlv_norm T.atT v b hbP hbQ
    have hmem : (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r) • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z) ∈ Ld D u 0 (Nat.zero_le _) c3 := by
      rw [hb', mul_smul]; exact Submodule.smul_mem _ _ hb
    refine ⟨r, hr, hmem, ?_⟩
    have hγz : γ.1.1 *ᵥ z ∈ Formalism.HermitianLatticesTheory.localization₂ (T.atT.Pv v) (clsCrd D u 0 (Nat.zero_le _) c) := by
      rw [← hl1]; exact mem_localization_of_mem₂ _ ⟨z, hz, rfl⟩
    obtain ⟨s, hs, hsz⟩ := (rlv_mem_locP _ _ _).1 hγz
    set R := algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r with hR
    have e4 : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (s • (R • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z))) = R • (s • (γ.1.1 *ᵥ z)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, eΓ, smul_comm]
    have e5 : γ.1.1 *ᵥ (s • (R • z)) = R • (s • (γ.1.1 *ᵥ z)) := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_comm]
    have hin : R • (s • (γ.1.1 *ᵥ z)) ∈ Lk T.atT 0 (Nat.zero_le _) v c := Submodule.mem_sup_left (Submodule.smul_mem _ R hsz)
    have hRz : R • z ∈ Ld D u 0 (Nat.zero_le _) c1 := Submodule.smul_mem _ _ hz
    obtain ⟨w3, hw3def⟩ : ∃ w3 : ↥(Ld D u 0 (Nat.zero_le _) c3), w3.1 = s • (R • ((Γ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z)) :=
      ⟨s • (⟨_, hmem⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)), rfl⟩
    obtain ⟨w1, hw1def⟩ : ∃ w1 : ↥(Ld D u 0 (Nat.zero_le _) c1), w1.1 = s • (R • z) :=
      ⟨s • (⟨R • z, hRz⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)), rfl⟩
    have hw3 : (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by rw [hw3def, e4]; exact hin
    have hw1 : γ.1.1 *ᵥ w1.1 ∈ Lk T.atT 0 (Nat.zero_le _) v c := by rw [hw1def, e5]; exact hin
    have hA := hf' w3 hw3
    have hB := hf1 w1 hw1
    have ew3 : w3 = s • (⟨_, hmem⟩ : ↥(Ld D u 0 (Nat.zero_le _) c3)) := Subtype.ext hw3def
    have ew1 : w1 = s • (⟨R • z, hRz⟩ : ↥(Ld D u 0 (Nat.zero_le _) c1)) := Subtype.ext hw1def
    have pA : T.lv0.pr v c3 w3 = T.atT.res v s • T.lv0.pr v c3 ⟨_, hmem⟩ := by rw [ew3, T.lv0.pr_smul]
    have pB : T.lv0.pr v c1 w1 = T.atT.res v s • T.lv0.pr v c1 ⟨R • z, hRz⟩ := by rw [ew1, T.lv0.pr_smul]
    rw [pA, map_smul] at hA
    rw [pB, map_smul] at hB
    have hres : T.atT.res v s ≠ 0 := fun h0 => hs (RingHom.mem_ker.2 h0)
    have key : T.atT.res v s • (D.fm u).fv 0 v c3 (T.lv0.pr v c3 ⟨_, hmem⟩) =
        T.atT.res v s • (D.fm u).fv 0 v c1 (T.lv0.pr v c1 ⟨R • z, hRz⟩) := by
      refine hA.trans (Eq.trans ?_ hB.symm)
      refine congrArg x (congrArg (T.lv0.prk v c) (Subtype.ext ?_))
      show (g' : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ w3.1 = γ.1.1 *ᵥ w1.1
      rw [hw3def, hw1def, e4, e5]
    exact smul_right_injective _ hres key
  have hloc := local_unitary_of_matching_zero T v c3 c1 Γ hΓU hUΓ hPΓ hPdΓ hF
  exact matching_move_mem_level_zero T v c c1 c2 c3 γ.1 γ2.1 γd η η2 δ κ κ2 κd hs1 hs2 hδv h1 h2 hrel hloc

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem dnDiaMatch0F_holds (T : Forms0 D u) : DnDiaMatch0F T := by
  intro v v' hvv a k hk δ hδ c γd hγd κd hrel
  obtain ⟨hLc, hLd⟩ := diamond_lattice_transport T v' k δ hδ c ((D.fm u).dil 0 v' a c) γd hγd κd hrel
  obtain ⟨z, hz⟩ := dni_exists_one T v c
  have e : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) = z.1 := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hz2 : ((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1 ∈ Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v' a c) :=
    dni_mem_of _ (dni_inv_eq γd hLd) z.2
  have hz2' : (D.fm u).fv 0 v ((D.fm u).dil 0 v' a c) (T.lv0.pr v ((D.fm u).dil 0 v' a c) ⟨_, hz2⟩) = 1 :=
    (diamond_class_function T v v' hvv k δ hδ c ((D.fm u).dil 0 v' a c) γd κd hrel z.1 z.2 hz2).trans hz
  have hgz : (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (⟨_, hz2⟩ : ↥(Ld D u 0 (Nat.zero_le _) ((D.fm u).dil 0 v' a c))).1 ∈ Ld D u 0 (Nat.zero_le _) c := by
    show (γd : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ (((γd⁻¹ : GL (Fin (D.R.N 0)) D.host.E) : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) *ᵥ z.1) ∈ _
    rw [e]; exact z.2
  have hgz' : (D.fm u).fv 0 v c (T.lv0.pr v c ⟨_, hgz⟩) = 1 := by
    rw [pr_congr T v c ⟨_, hgz⟩ z e]; exact hz
  have hte := dniEquiv_te T v ((D.fm u).dil 0 v' a c) c γd hLc hLd ⟨_, hz2⟩ hz2' hgz hgz'
  have hne0 : ∀ {c0 : (D.mem u).C.cls 0} (x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c0)),
      x ((D.fm u).te 0 v c0) = 1 → x ≠ 0 := by
    intro c0 x hx h0
    rw [h0, LinearMap.zero_apply] at hx
    exact zero_ne_one hx
  choose γ1 η1 κ1 hs1 hr1 hl1 hf1 ht1 using fun x : {x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) //
    x ((D.fm u).te 0 v c) = 1} => T.down_natural_level_zero v c x.1 (hne0 x.1 x.2)
  choose γ2 η2 κ2 hs2 hr2 hl2 hf2 ht2 using fun x : {x : Module.Dual ((D.mem u).A.Fv v)
    ((D.fm u).lk 0 v ((D.fm u).dil 0 v' a c)) // x ((D.fm u).te 0 v ((D.fm u).dil 0 v' a c)) = 1} =>
    T.down_natural_level_zero v ((D.fm u).dil 0 v' a c) x.1 (hne0 x.1 x.2)
  refine ⟨dualSigma (dniEquiv T v ((D.fm u).dil 0 v' a c) c γd hLc hLd) _ _ hte, η1, η2,
    fun x => ⟨γ1 x, κ1 x, hs1 x, hr1 x, fun h => ?_⟩, fun x => ⟨γ2 x, κ2 x, hs2 x, hr2 x, fun h => ?_⟩, fun x => ?_⟩
  · funext s
    rw [ht1 x h s _ (is_translate_inverse T (γ1 x) s), Units.val_inv_eq_inv_val]
    rfl
  · funext s
    rw [ht2 x h s _ (is_translate_inverse T (γ2 x) s), Units.val_inv_eq_inv_val]
    rfl
  · exact dn_match_one T v v' hvv k δ hδ c _ _ _ γd hγd κd hrel hLc hLd x.1 _
      (fun w => dualSigma_apply _ _ _ hte x w) (γ1 x) (γ2 _) (η1 x) (η2 _) (κ1 x) (κ2 _) (hs1 x) (hs2 _)
      (hr1 x) (hr2 _) (hl1 x) (hl2 _) (hf1 x) (hf2 _)

theorem dnMatchAll_holds : DnMatchAll := fun _ _ T => dnDiaMatch0F_holds T

end CrossDiaZero

end
end
