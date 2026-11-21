import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueLiftOfNilpotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueHom

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerHom

theorem exists_roots {R : Type} [CommRing R] {l : ℕ} (h : ∀ x : R, ∃ y, y ^ l = x) (u : R) :
    ∃ y : ℕ → R, y 0 = u ∧ ∀ m, y (m + 1) ^ l = y m := by
  choose r hr using h
  exact ⟨fun m => Nat.rec u (fun _ z => r z) m, rfl, fun m => hr _⟩

theorem roots_unique {R : Type} [CommRing R] {l : ℕ} (h : ∀ x y : R, x ^ l = y ^ l → x = y) {y z : ℕ → R}
    (h0 : y 0 = z 0) (hy : ∀ m, y (m + 1) ^ l = y m) (hz : ∀ m, z (m + 1) ^ l = z m) (m : ℕ) : y m = z m := by
  induction m with
  | zero => exact h0
  | succ m ih => exact h _ _ (by rw [hy, hz, ih])

theorem pow_sub_pow {R : Type} [CommRing R] {l : ℕ} (F : R →+* R) (hF : ∀ x, F x = x ^ l) (x y : R) (m : ℕ) :
    x ^ l ^ m - y ^ l ^ m = (x - y) ^ l ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ l m, pow_mul, pow_mul, pow_mul, ← ih, ← hF, ← hF, ← hF, map_sub]

theorem iter_root {R : Type} [CommRing R] {l : ℕ} {x : ℕ → R} (hx : ∀ m, x (m + 1) ^ l = x m) (m : ℕ) :
    x m ^ l ^ m = x 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ' l m, pow_mul, hx, ih]

variable {l : ℕ} [Fact l.Prime]

theorem pow_char (A : PAlg l) (x : A.A) : A.frob x = x ^ l := rfl

theorem pow_inj (A : PAlg l) (x y : A.A) (h : x ^ l = y ^ l) : x = y := A.frob_bijective.1 h

theorem pow_surj (A : PAlg l) (x : A.A) : ∃ y, y ^ l = x := A.frob_bijective.2 x

theorem eq_of_roots_mod (A : PAlg l) {x y : ℕ → A.A} (hx : ∀ m, x (m + 1) ^ l = x m) (hy : ∀ m, y (m + 1) ^ l = y m)
    (h : ∀ m, x m - y m ∈ Ideal.span {A.pi}) : x 0 = y 0 := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hH : IsHausdorff (Ideal.span {A.s (pFlat l)}) A.A := A.compl.toIsHausdorff
  refine sub_eq_zero.1 (hH.haus' _ fun n => ?_)
  rw [SModEq.zero, Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id, ← iter_root hx n, ← iter_root hy n,
    pow_sub_pow A.frob (pow_char A)]
  exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl).le (Ideal.pow_mem_pow (h n) _)

theorem mapU_mem {A A' : PAlg l} (φ : A ⟶ A') {x : A.U} (hx : x ∈ Ideal.span {(l : A.U)}) :
    mapU φ x ∈ Ideal.span {(l : A'.U)} := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_sharp_cong (A : PAlg l) (x : A.U) : ∃ a, A.sharp a - x ∈ Ideal.span {(l : A.U)} := by
  obtain ⟨a, ha⟩ := (RL.u_mod A).1 (Ideal.Quotient.mk _ x)
  refine ⟨a, ?_⟩
  rw [A.sharpMap_eq] at ha
  simpa using Ideal.Quotient.eq.1 ha

def modEquiv (A : PAlg l) : (A.A ⧸ Ideal.span {A.pi}) ≃+* A.Un 1 :=
  (Ideal.quotEquivOfEq (RL.u_mod A).2.symm).trans (RingHom.quotientKerEquivOfSurjective (RL.u_mod A).1)

theorem modEquiv_mk (A : PAlg l) (a : A.A) : modEquiv A (Ideal.Quotient.mk _ a) = A.aToU1 a := rfl

def gBar (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) : R →+* A.A ⧸ Ideal.span {A.pi} :=
  ((modEquiv A).symm : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi}).comp ((Ideal.Quotient.mk _).comp g)

theorem gBar_iff (A : PAlg l) {R : Type} [CommRing R] (g : R →+* A.U) (r : R) (a : A.A) :
    gBar A g r = Ideal.Quotient.mk _ a ↔ A.sharp a - g r ∈ Ideal.span {(l : A.U)} := by
  have e : gBar A g r = (modEquiv A).symm (Ideal.Quotient.mk _ (g r)) := rfl
  rw [e, RingEquiv.symm_apply_eq, modEquiv_mk, A.sharpMap_eq, eq_comm, Ideal.Quotient.eq, pow_one]

open CrystallineSemistableComparison.PAlg in

theorem core {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (A' : PAlg l)
    (g : s.R →+* A'.U) (hga : g.comp s.a = A'.oC.comp κ) (u : Fin d → A'.A) (hu : ∀ k, A'.sharp (u k) = g (s.T k)) :
    ∃ φ : 𝒯.A ⟶ A', ((mapU φ).comp 𝒯.g = g ∧ ∀ k, Hom.f φ (𝒯.c k 0).val = u k) ∧
      ∀ φ' : 𝒯.A ⟶ A', (mapU φ').comp 𝒯.g = g → (∀ k, Hom.f φ' (𝒯.c k 0).val = u k) → φ' = φ := by
  have hy : ∀ k, ∃ y : ℕ → A'.A, y 0 = u k ∧ ∀ m, y (m + 1) ^ l = y m := fun k => exists_roots (pow_surj A') (u k)
  choose y hy0 hys using hy
  have hc : ∀ k m, ((𝒯.c k (m + 1)).val) ^ l = (𝒯.c k m).val := fun k m => by
    rw [← Units.val_pow_eq_pow_val, 𝒯.c_succ]
  have ho : ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (pFlat l) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have h1 : ∀ x w, theta0 l w = κ x → gBar A' g (s.a x) = ((Ideal.Quotient.mk (Ideal.span {A'.pi})).comp A'.s) (w.coeff 0) := by
    intro x w hw
    have hcf : (A'.sW w).coeff 0 = A'.s (w.coeff 0) := WittVector.map_coeff _ _ _
    refine (gBar_iff A' g _ _).2 ?_
    have e1 : g (s.a x) = A'.th (A'.sW w) := by
      rw [← A'.oC_theta0, hw]
      exact RingHom.congr_fun hga x
    have e2 := A'.sharpMap_coeff (A'.sW w)
    rw [hcf, A'.sharpMap_eq] at e2
    rw [e1]
    simpa using Ideal.Quotient.eq.1 e2
  have h2 : ∀ k, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k 0) = gBar A' g (s.T k) := fun k =>
    ((gBar_iff A' g _ _).2 (by rw [hy0, hu, sub_self]; exact Ideal.zero_mem _)).symm
  have h3 : ∀ k m, Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k (m + 1)) ^ l = Ideal.Quotient.mk (Ideal.span {A'.pi}) (y k m) :=
    fun k m => by rw [← map_pow, hys]
  obtain ⟨f, ⟨hfo, hfg, hfc⟩, hfu⟩ := 𝒯.univ (A'.A ⧸ Ideal.span {A'.pi}) ((Ideal.Quotient.mk _).comp A'.s) (gBar A' g)
    (fun k m => Ideal.Quotient.mk _ (y k m)) ho h1 h2 h3
  obtain ⟨φ, hφ, hφu⟩ := GlobalTheory.CompanionTheory.PerfLift.existsUnique_hom 𝒯.A A' f hfo
  have hφa : ∀ a, Ideal.Quotient.mk (Ideal.span {A'.pi}) (Hom.f φ a) = f a := fun a => RingHom.congr_fun hφ a
  have hck : ∀ k, Hom.f φ (𝒯.c k 0).val = u k := by
    intro k
    rw [← hy0 k]
    refine eq_of_roots_mod A' (x := fun m => Hom.f φ (𝒯.c k m).val) (fun m => ?_) (hys k) fun m => ?_
    · rw [← map_pow, hc]
    · refine Ideal.Quotient.eq.1 ?_
      rw [hφa, hfc]
  have hgφ : (mapU φ).comp 𝒯.g = g := by
    have hE := GlobalTheory.CompanionTheory.EtaleLift.etLift_of_isAdicComplete (Ideal.span {(l : A'.U)}) A'.completeU
      (MvPolynomial (Fin d) O) s.R (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R)) s.et
      (g.comp (MvPolynomial.eval₂Hom s.a fun k => (s.T k : s.R))) ((Ideal.Quotient.mk _).comp g) rfl
    refine hE.unique ⟨?_, ?_⟩ ⟨rfl, rfl⟩
    · refine MvPolynomial.ringHom_ext (fun o => ?_) fun k => ?_
      · have e1 : 𝒯.g (s.a o) = 𝒯.A.oC (κ o) := RingHom.congr_fun 𝒯.hg o
        have e2 : g (s.a o) = A'.oC (κ o) := RingHom.congr_fun hga o
        simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
        rw [e1, e2, mapU_oC]
      · simp only [RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        rw [← 𝒯.c_sharp, mapU_sharp, hck, hu]
    · refine RingHom.ext fun r => ?_
      obtain ⟨a, ha⟩ := exists_sharp_cong 𝒯.A (𝒯.g r)
      have e : gBar A' g r = Ideal.Quotient.mk _ (Hom.f φ a) := by rw [hφa]; exact (hfg r a ha).symm
      have e1 := (gBar_iff A' g r _).1 e
      have e2 := mapU_mem φ ha
      rw [map_sub, mapU_sharp] at e2
      refine Ideal.Quotient.eq.2 ?_
      have e3 : mapU φ (𝒯.g r) - g r = (A'.sharp (Hom.f φ a) - g r) - (A'.sharp (Hom.f φ a) - mapU φ (𝒯.g r)) := by ring
      change mapU φ (𝒯.g r) - g r ∈ _
      rw [e3]
      exact Ideal.sub_mem _ e1 e2
  refine ⟨φ, ⟨hgφ, hck⟩, fun φ' hg' hk' => hφu φ' (hfu _ ⟨?_, ?_, ?_⟩)⟩
  · rw [RingHom.comp_assoc, Hom.comm]
  · intro r a ha
    have e2 := mapU_mem φ' ha
    rw [map_sub, mapU_sharp] at e2
    have e3 : mapU φ' (𝒯.g r) = g r := RingHom.congr_fun hg' r
    rw [e3] at e2
    exact ((gBar_iff A' g r _).2 e2).symm
  · intro k m
    have := roots_unique (pow_inj A') (y := fun m => Hom.f φ' (𝒯.c k m).val) (z := y k)
      ((hk' k).trans (hy0 k).symm) (fun m => by
        rw [← map_pow, hc]) (hys k) m
    exact congrArg (Ideal.Quotient.mk _) this

theorem tower_hom : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  intro l _ O _ F κ d s 𝒯 T
  obtain ⟨g, hg, hgu⟩ := s.univ (CommRingCat.of T.1.U) T.2.1 (T.1.oC.comp κ) T.2.2
  have hga : g.comp s.a = T.1.oC.comp κ :=
    F.ov_uniq (hg ▸ F.ov_map (CommRingCat.ofHom g) s.ov) T.2.2
  have hall : ∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g := by
    intro φ
    refine hgu _ ?_
    have h1 : F.Pt.map (CommRingCat.ofHom (mapU φ.1)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1 :=
      congrArg Subtype.val φ.2
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ.1).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [CommRingCat.ofHom_comp, F.Pt.map_comp]
      exact h1
    exact h2
  refine ⟨g, hg, hall, fun u hu => ?_⟩
  obtain ⟨φ, ⟨hφg, hφk⟩, hφu⟩ := core 𝒯 T.1 g hga u hu
  have hpt : (F.pt κ).map φ 𝒯.obj.2 = T.2 := by
    refine Subtype.ext ?_
    change F.Pt.map (CommRingCat.ofHom (mapU φ)) (F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀) = T.2.1
    have h2 : F.Pt.map (CommRingCat.ofHom ((mapU φ).comp 𝒯.g)) s.y₀ = T.2.1 := by
      rw [hφg]
      exact hg
    rw [CommRingCat.ofHom_comp, F.Pt.map_comp] at h2
    exact h2
  refine ⟨⟨φ, hpt⟩, hφk, fun φ' hk => Subtype.ext (hφu φ'.1 (hall φ') hk)⟩

end GlobalTheory.CompanionTheory.TowerHom
end
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_point_universal_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  first | exact @GlobalTheory.CompanionTheory.TowerHom.tower_hom | exact GlobalTheory.CompanionTheory.TowerHom.tower_hom | (intros; apply GlobalTheory.CompanionTheory.TowerHom.tower_hom <;> assumption)
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerAct

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}

def val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : T.1.A :=
  PAlg.Hom.f φ.1 (𝒯.c k 0).val

theorem val_comp (𝒯 : Tower κ s) {T T' : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (ψ : T ⟶ T') (k : Fin d) :
    val 𝒯 (φ ≫ ψ) k = PAlg.Hom.f ψ.1 (val 𝒯 φ k) := rfl

theorem sharp_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    T.1.sharp (val 𝒯 φ k) = mapU φ.1 (𝒯.g (s.T k)) := by
  rw [val, ← mapU_sharp]
  exact congrArg (mapU φ.1) (𝒯.c_sharp k)

def valU (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : (T.1.A)ˣ :=
  Units.map (PAlg.Hom.f φ.1).toMonoidHom (𝒯.c k 0)

theorem valU_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    ((valU 𝒯 φ k : (T.1.A)ˣ) : T.1.A) = val 𝒯 φ k := rfl

theorem hom_ext (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T)
    (h : ∀ k, val 𝒯 φ k = val 𝒯 ψ k) : φ = ψ := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, -, hχ⟩ := huniq (fun k => val 𝒯 φ k) hu
  exact (hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm

theorem sharp_mem (ε : Eps l) {T : (F.pt κ).Elements} (x : (epsU ε (F.pt κ)).U T) :
    T.1.sharp ((x.1 : (T.1.A)ˣ) : T.1.A) = 1 := by
  have hx : Units.map T.1.sharp x.1 = 1 := x.2
  exact congrArg Units.val hx

theorem exists_act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) :
    ∃ ψ : 𝒯.obj ⟶ T, ∀ k, val 𝒯 ψ k = ((a k).1 : T.1.A) * val 𝒯 φ k := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [map_mul, sharp_mem ε (a k), one_mul, sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, hχ, -⟩ := huniq _ hu
  exact ⟨χ, fun k => hχ k⟩

def act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) : 𝒯.obj ⟶ T :=
  (exists_act 𝒯 ε a φ).choose

theorem act_val (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    val 𝒯 (act 𝒯 ε a φ) k = ((a k).1 : T.1.A) * val 𝒯 φ k :=
  (exists_act 𝒯 ε a φ).choose_spec k

theorem exists_quot (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T) :
    ∃ a : Fin d → (epsU ε (F.pt κ)).U T, ∀ k, ((a k).1 : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k := by
  obtain ⟨g, -, hg, -⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k) := fun χ k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg χ) _
  refine ⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩
  · show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]
  · show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k
    rw [← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]

theorem act_unique (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a b : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (h : act 𝒯 ε a φ = act 𝒯 ε b φ) : a = b := by
  funext k
  have h1 := act_val 𝒯 ε a φ k
  rw [h, act_val, ← valU_val 𝒯 φ k] at h1
  apply Subtype.ext
  apply Units.ext
  exact ((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm

theorem tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val := by
  intro l _ O _ F κ d s 𝒯 ε
  refine ⟨{ act := fun a φ => act 𝒯 ε a φ
            act_one := fun c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val]
              exact one_mul _
            act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val, act_val, act_val, ← mul_assoc]
              rfl
            act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by
              rw [val_comp, act_val, act_val, val_comp, map_mul]
              rfl
            ne := fun t => by
              obtain ⟨g, -, -, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 ((jE (F.pt κ)).obj t)
              choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))
              obtain ⟨χ, -, -⟩ := huniq u hu
              exact ⟨χ⟩
            trans := fun t c c' => by
              obtain ⟨a, ha⟩ := exists_quot 𝒯 ε c c'
              have hac : act 𝒯 ε a c = c' := hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]
              exact ⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩
  intro T a φ k
  exact act_val 𝒯 ε a φ k

end GlobalTheory.CompanionTheory.TowerAct
end
end
