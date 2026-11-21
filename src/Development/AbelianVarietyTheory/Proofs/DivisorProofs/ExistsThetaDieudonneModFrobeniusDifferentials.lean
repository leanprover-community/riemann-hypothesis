import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasis

section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonneFunctorBase_functor_properties : ∀ (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) (B : Base p P) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H K : PDivGroup p k) (hG : P k G) (hH : P k H) (hK : P k K), B.map hG hG (𝟙 G) = LinearMap.id ∧ (∀ (f : G ⟶ H) (g : H ⟶ K), B.map hG hK (f ≫ g) = B.map hG hH f ∘ₗ B.map hH hK g) ∧ (∀ f g : G ⟶ H, B.map hG hH (f + g) = B.map hG hH f + B.map hG hH g) ∧ B.map hG hH (0 : G ⟶ H) = 0 ∧ (∀ (n : ℕ) (f : G ⟶ H) (m : B.M H hH), B.map hG hH ((p : ℤ_[p]) ^ n • f) m = p ^ n • B.map hG hH f m) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.red G hG (B.map hG hH f m) = rigExtMap f (B.red H hH m)) ∧ (∀ (f : G ⟶ H) (m : B.M H hH), B.map hG hH f (B.F H hH m) = B.F G hG (B.map hG hH f m)) ∧ Module.finrank (WittVector p k) (B.M G hG) = G.height ∧ ∀ (n : ℕ) (m : B.M G hG), p ^ n • m = 0 → m = 0 := by
  first | exact @GlobalTheory.Dieu.base_functor_props | exact GlobalTheory.Dieu.base_functor_props | (intros; apply GlobalTheory.Dieu.base_functor_props <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem wittMap_frobRing_bijective (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] : Function.Bijective (WittVector.map (p := p) (frobRing (p_eq_zero p k))) := by
  have hb : Function.Bijective (frobRing (p_eq_zero p k)) := by
    have e : ⇑(frobRing (p_eq_zero p k)) = ⇑(frobenius k p) :=
      funext fun r => by rw [frobRing_apply, frobenius_def]
    rw [e]
    exact bijective_frobenius k p
  exact ⟨WittVector.map_injective _ hb.1, WittVector.map_surjective _ hb.2⟩

theorem bijective_of_basis {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R' M'] (σ : R →+* R') (hσ : Function.Bijective σ) (f : M →+ M')
    (hf : ∀ (a : R) (m : M), f (a • m) = σ a • f m) {ι : Type} [Fintype ι] (b : Module.Basis ι R M)
    (b' : Module.Basis ι R' M') (hb : ∀ i, b' i = f (b i)) : Function.Bijective f := by
  have key : ∀ c : ι → R, f (∑ i, c i • b i) = ∑ i, σ (c i) • b' i := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hb]
  refine ⟨(injective_iff_map_eq_zero f).2 fun m hm => ?_, fun x => ?_⟩
  · rw [← b.sum_repr m, key] at hm
    have : ∀ i, b.repr m i = 0 := fun i => by
      have := Fintype.linearIndependent_iff.1 b'.linearIndependent _ hm i
      exact hσ.1 (this.trans (map_zero σ).symm)
    rw [← b.sum_repr m]
    simp [this]
  · obtain ⟨c, hc⟩ : ∃ c : ι → R, ∀ i, σ (c i) = b'.repr x i :=
      ⟨fun i => Function.surjInv hσ.2 (b'.repr x i), fun i => Function.surjInv_eq hσ.2 _⟩
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [key]
    simp only [hc]
    exact b'.sum_repr x

end GlobalTheory.Dieu

theorem GlobalTheory.Dieu.frobTwist_module : ∀ (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧ (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧ ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n = B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  intro p _ B k _ _ _ G
  have h2 : ∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G)
      (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m := fun m =>
    (B.smap_comp trivial trivial trivial (frobProj (p_eq_zero p k) G)
      (SemiHom.ofHom (relFrob (p_eq_zero p k) G)) (absFrob (p_eq_zero p k) G)
      (fun n a => by rw [SemiHom.ofHom_app, relFrob_app_frobProj, absFrob_app]) m).symm
  refine ⟨?_, h2, fun m n e => ?_⟩
  · haveI := B.free G trivial
    haveI := B.finite G trivial
    letI := (frobRing (p_eq_zero p k)).toAlgebra
    obtain ⟨b', hb'⟩ := GlobalTheory.T.dieudonne_baseChange_basis p (fun _ _ _ => True) B k k G trivial trivial _
      (Module.Free.chooseBasis (WittVector p k) (B.M G trivial))
    exact bijective_of_basis _ (wittMap_frobRing_bijective p k) _
      (fun a m => B.smap_smul trivial trivial _ a m) _ b' hb'
  · obtain ⟨-, hc, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G
      (frobTwist (p_eq_zero p k) G) G trivial trivial trivial
    obtain ⟨hid, -, -, -, hp, -⟩ := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) B k G G G trivial trivial trivial
    rw [← h2, e, ← LinearMap.comp_apply, ← hc, relFrob_comp_verschiebung, ← pow_one (p : ℤ_[p]), hp,
      pow_one, hid, LinearMap.id_apply]
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius : ∀ (p : ℕ) [Fact p.Prime] (B : Base p fun _ _ _ => True) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Bijective (B.smap trivial trivial (frobProj (p_eq_zero p k) G)) ∧ (∀ m, B.map trivial trivial (relFrob (p_eq_zero p k) G) (B.smap trivial trivial (frobProj (p_eq_zero p k) G) m) = B.F G trivial m) ∧ ∀ m n, B.smap trivial trivial (frobProj (p_eq_zero p k) G) n = B.map trivial trivial (verschiebung (p_eq_zero p k) G) m → B.F G trivial n = p • m := by
  atlas_forward_decl GlobalTheory.Dieu.frobTwist_module
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem theory_V_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧ (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) = T.map (verschiebung (p_eq_zero p k) G) m) ∧ (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G), (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), T.map f (T.V H m) = T.V G (T.map f m) := by
  intro p _ T k _ _ _ G

  have tor : ∀ (K : PDivGroup p k) (m : T.M K), p • m = 0 → m = 0 := by
    intro K m hm
    have h := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k K K K trivial trivial trivial).2.2.2.2.2.2.2.2 1 m
    exact h (by simpa using hm)
  have Finj : ∀ K : PDivGroup p k, Function.Injective (T.F K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.V_F K x, ← T.V_F K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have Vinj : ∀ K : PDivGroup p k, Function.Injective (T.V K) := by
    intro K x y hxy
    have h1 : p • x = p • y := by rw [← T.F_V K x, ← T.F_V K y]; exact congrArg _ hxy
    have : p • (x - y) = 0 := by rw [smul_sub, h1, sub_self]
    exact sub_eq_zero.mp (tor K _ this)
  have comm : ∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G),
      (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m) := by
    intro H φ hφ m
    apply Finj G
    rw [← hφ, T.F_V H m, T.F_V G, map_nsmul]
  refine ⟨Finj G, Vinj G, ?_, comm, ?_⟩
  · intro m
    have ht := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
    obtain ⟨n, hn⟩ := ht.1.2 (T.map (verschiebung (p_eq_zero p k) G) m)
    have hF : T.F G n = p • m := ht.2.2 m n hn
    have : n = T.V G m := Finj G (by rw [hF, T.F_V])
    rw [← this]; exact hn
  · intro H f m
    exact comm H (T.map f)
      (fun m => (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H H trivial trivial trivial).2.2.2.2.2.2.1 f m) m

end GlobalTheory.Dieu
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), Function.Injective (T.F G) ∧ Function.Injective (T.V G) ∧ (∀ m, T.smap (frobProj (p_eq_zero p k) G) (T.V G m) = T.map (verschiebung (p_eq_zero p k) G) m) ∧ (∀ (H : PDivGroup p k) (φ : T.M H →ₗ[(WittVector p k)] T.M G), (∀ m, φ (T.F H m) = T.F G (φ m)) → ∀ m, φ (T.V H m) = T.V G (φ m)) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), T.map f (T.V H m) = T.V G (T.map f m) := by
  atlas_forward_decl GlobalTheory.Dieu.theory_V_verschiebung
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.Theory

theorem frobProj_omega_surjective {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (G : PDivGroup p k) : Function.Surjective (frobProj (p_eq_zero p k) G).omega := by
  letI := (frobRing (p_eq_zero p k)).toAlgebra
  intro t
  obtain ⟨x, rfl⟩ := (omega_baseChange_bijective G k (p_eq_zero p k)).2 t
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero _).trans (map_zero _).symm⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, (map_add _ a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add _ x y).symm)⟩
  | tmul r w =>
    refine ⟨(frobeniusEquiv k p).symm r • w, ?_⟩
    rw [liftSemi_tmul, map_smulₛₗ]
    congr 1
    show frobRing (p_eq_zero p k) _ = r
    rw [frobRing_apply, frobeniusEquiv_symm_pow_p]

theorem hodge_filtration : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  intro p _ T k _ _ _ G
  obtain ⟨-, hVinj, hVsm, -, -⟩ := GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G
  obtain ⟨hbij, -, -⟩ := GlobalTheory.T.dieudonne_frobeniusTwist_bijective_relFrobenius p T.base k G
  obtain ⟨-, -, -, hver, -, -, -⟩ := rigExt_field_of_charP p k (p_eq_zero p k) G
  have key : ∀ m, (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) =
      rigExtMap (verschiebung (p_eq_zero p k) G) (T.red G m) := by
    intro m
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), hVsm]
    rw [← SemiHom.ofHom_rig]
    exact T.base.red_smap trivial trivial (SemiHom.ofHom _) m
  have rinj : Function.Injective (frobProj (p_eq_zero p k) G).rig := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial x
    rw [← T.base.red_smap trivial trivial (frobProj (p_eq_zero p k) G), T.base.red_eq_zero] at hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨n', rfl⟩ := hbij.2 n
    have hm : m = p • n' := hbij.1 (by rw [hn, map_nsmul])
    exact (T.base.red_eq_zero G trivial m).2 ⟨n', hm⟩
  have osurj := frobProj_omega_surjective G
  have h1 : ∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega := by
    intro x
    constructor
    · rintro ⟨m, rfl⟩
      have hm : (frobProj (p_eq_zero p k) G).rig (T.red G (T.V G m)) ∈
          LinearMap.range (frobTwist (p_eq_zero p k) G).rigOfOmega := by
        rw [key, ← hver]; exact ⟨_, rfl⟩
      obtain ⟨w', hw'⟩ := hm
      obtain ⟨w, rfl⟩ := osurj w'
      exact ⟨w, rinj ((SemiHom.rig_rigOfOmega _ w).trans hw')⟩
    · rintro ⟨w, rfl⟩
      have hw : (frobTwist (p_eq_zero p k) G).rigOfOmega ((frobProj (p_eq_zero p k) G).omega w) ∈
          LinearMap.range (rigExtMap (verschiebung (p_eq_zero p k) G)) := by
        rw [hver]; exact ⟨_, rfl⟩
      obtain ⟨y, hy⟩ := hw
      obtain ⟨m, rfl⟩ := T.base.red_surjective G trivial y
      exact ⟨m, rinj ((key m).trans (hy.trans (SemiHom.rig_rigOfOmega _ w).symm))⟩
  have h2 : ∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n := by
    intro m
    refine (T.base.red_eq_zero G trivial _).trans ⟨fun ⟨n, hn⟩ => ⟨n, hVinj ?_⟩, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
    · rw [hn]; exact (T.V_F G n).symm
    · rw [hn]; exact T.V_F G n
  refine ⟨h1, h2, fun m => ?_, G.rigOfOmega_injective_of_eq_zero (p_eq_zero p k)⟩
  rw [G.exact_rigOfOmega_rigToLie (p_eq_zero p k) (T.red G m)]
  constructor
  · intro hm
    obtain ⟨m', hm'⟩ := (h1 _).2 (by simpa using hm)
    have h0 : T.red G (m - T.V G m') = 0 := by rw [map_sub, hm', sub_self]
    obtain ⟨n, hn⟩ := (T.base.red_eq_zero G trivial _).1 h0
    refine ⟨m' + T.F G n, ?_⟩
    rw [map_add, T.V_F G n, ← hn, add_sub_cancel]
  · rintro ⟨n, rfl⟩
    obtain ⟨w, hw⟩ := (h1 (T.red G (T.V G n))).1 ⟨n, rfl⟩
    exact ⟨w, hw⟩

end GlobalTheory.Dieu.Theory
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dieudonne_hodgeFiltration_perfectField : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), (∀ x : G.RigExt, (∃ m, T.red G (T.V G m) = x) ↔ x ∈ LinearMap.range G.rigOfOmega) ∧ (∀ m, T.red G (T.V G m) = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ m, G.rigToLie (p_eq_zero p k) (T.red G m) = 0 ↔ ∃ n, m = T.V G n) ∧ Function.Injective G.rigOfOmega := by
  atlas_forward_decl GlobalTheory.Dieu.Theory.hodge_filtration
end

section
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Theory

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def redVToRange (G : PDivGroup p k) : T.M G →+ LinearMap.range G.rigOfOmega :=
  AddMonoidHom.codRestrict ((T.red G).toAddMonoidHom.comp (T.V G).toAddMonoidHom)
    (LinearMap.range G.rigOfOmega) fun m =>
      ((GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).1 (T.red G (T.V G m))).1 ⟨m, rfl⟩

def theta (G : PDivGroup p k) : T.M G →+ G.omega :=
  (LinearEquiv.ofInjective G.rigOfOmega (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2).symm.toLinearMap.toAddMonoidHom.comp
    (T.redVToRange G)

theorem rigOfOmega_theta (G : PDivGroup p k) (m : T.M G) :
    G.rigOfOmega (T.theta G m) = T.red G (T.V G m) := by
  have inj := (GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G).2.2.2
  show G.rigOfOmega ((LinearEquiv.ofInjective G.rigOfOmega inj).symm (T.redVToRange G m)) = _
  have h := congrArg Subtype.val
    ((LinearEquiv.ofInjective G.rigOfOmega inj).apply_symm_apply (T.redVToRange G m))
  rw [LinearEquiv.ofInjective_apply] at h
  exact h

theorem theta_spec (G : PDivGroup p k) :
    (∀ m, G.rigOfOmega (T.theta G m) = T.red G (T.V G m)) ∧ Function.Surjective (T.theta G) ∧
      (∀ m, T.theta G m = 0 ↔ ∃ n, m = T.F G n) ∧
      (∀ (a : WittVector p k) m, T.theta G (WittVector.frobenius a • m) =
        WittVector.constantCoeff a • T.theta G m) ∧
      ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H),
        T.theta G (T.map f m) = omegaMap G H f (T.theta H m) := by
  have hG := GlobalTheory.T.dieudonne_hodgeFiltration_perfectField p T k G
  have inj := hG.2.2.2
  refine ⟨T.rigOfOmega_theta G, fun w => ?_, fun m => ?_, fun a m => ?_, fun H f m => ?_⟩
  · obtain ⟨m, hm⟩ := (hG.1 (G.rigOfOmega w)).2 ⟨w, rfl⟩
    exact ⟨m, inj (by rw [T.rigOfOmega_theta, hm])⟩
  · rw [← hG.2.1 m, ← T.rigOfOmega_theta G m]
    exact ⟨fun h => by rw [h, map_zero], fun h => inj (by rw [h, map_zero])⟩
  · apply inj
    rw [T.rigOfOmega_theta, G.rigOfOmega.map_smul, T.rigOfOmega_theta, (T.V G).map_smulₛₗ,
      ← WittVector.frobeniusEquiv_apply, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply,
      (T.red G).map_smulₛₗ]
  · apply inj
    have hV := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).2.2.2.2 H f m
    have hF := (GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G H H trivial trivial trivial).2.2.2.2.2.1 f
      (T.V H m)
    rw [T.rigOfOmega_theta, ← hV]
    rw [show T.red G (T.map f (T.V H m)) = rigExtMap f (T.red H (T.V H m)) from hF,
      ← T.rigOfOmega_theta H m, rigExtMap_rigOfOmega]

end GlobalTheory.Dieu.Theory

theorem GlobalTheory.Dieu.theta_exists : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p], ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega, ∀ G : PDivGroup p k, (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧ Function.Surjective (θ G) ∧ (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ (a : (WittVector p k)) m, θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), θ G (T.map f m) = omegaMap G H f (θ H m) :=
  fun _ _ T _ _ _ _ => ⟨fun G => T.theta G, fun G => T.theta_spec G⟩
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_dieudonne_mod_frobenius_differentials : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p], ∃ θ : ∀ G : PDivGroup p k, T.M G →+ G.omega, ∀ G : PDivGroup p k, (∀ m, G.rigOfOmega (θ G m) = T.red G (T.V G m)) ∧ Function.Surjective (θ G) ∧ (∀ m, θ G m = 0 ↔ ∃ n, m = T.F G n) ∧ (∀ (a : (WittVector p k)) m, θ G (WittVector.frobenius a • m) = WittVector.constantCoeff a • θ G m) ∧ ∀ (H : PDivGroup p k) (f : G ⟶ H) (m : T.M H), θ G (T.map f m) = omegaMap G H f (θ H m) := by
  atlas_forward_decl GlobalTheory.Dieu.theta_exists
end
