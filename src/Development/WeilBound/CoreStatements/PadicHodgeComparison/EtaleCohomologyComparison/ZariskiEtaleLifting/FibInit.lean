import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

theorem resLe_cls_zero {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ) (a : K.X n) (ha : K.d n a = 0)
    (h : a ∈ K.B n) : K.cls a ha = 0 := ((CrystallineSemistableComparison.P.cls_surj K n).2.1 a ha).2 h

theorem resLe_cls_smul {R : Type} [CommRing R] (K : Cx.{w} R) (n : ℕ) (r : R) (a : K.X n) (ha : K.d n a = 0)
    (hb : K.d n (r • a) = 0) : K.cls (r • a) hb = r • K.cls a ha := (CrystallineSemistableComparison.P.cls_surj K n).2.2.2.2 r a ha hb

theorem eq_zero_of_mem_boundaries_zero {R : Type} [CommRing R] (K : Cx.{w} R) (a : K.X 0) (h : a ∈ K.B 0) : a = 0 :=
  (Submodule.mem_bot R).1 h

theorem resLe_succ {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    (n : ℕ) (hK : ExactUpTo (1 : R) (K.d n) (K.d (n + 1))) (s : R) :
    UpTo s (φ.mapH (n + 1)) ↔ ExactUpTo s (L.d n) (L.d (n + 1)) := by
  have hz : ∀ x : K.H (n + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K (n + 1)).1 x
    obtain ⟨b, hb⟩ := hK a ha
    exact resLe_cls_zero K (n + 1) a ha ⟨b, by rw [hb, one_smul]⟩
  constructor
  · rintro ⟨-, hs⟩ y hy
    obtain ⟨x, hx⟩ := hs (L.cls y hy)
    rw [hz x, map_zero] at hx
    have hy' : L.d (n + 1) (s • y) = 0 := by rw [map_smul, hy, smul_zero]
    rw [← resLe_cls_smul L (n + 1) s y hy hy'] at hx
    have : s • y ∈ L.B (n + 1) := ((CrystallineSemistableComparison.P.cls_surj L (n + 1)).2.1 _ hy').1 hx.symm
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc⟩
  · intro h
    refine ⟨fun x _ => by rw [hz x, smul_zero], fun y => ⟨0, ?_⟩⟩
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L (n + 1)).1 y
    have hb' : L.d (n + 1) (s • b) = 0 := by rw [map_smul, hb, smul_zero]
    obtain ⟨c, hc⟩ := h b hb
    rw [map_zero, ← resLe_cls_smul L (n + 1) s b hb hb']
    exact (resLe_cls_zero L (n + 1) _ hb' ⟨c, hc⟩).symm

theorem resLe_zero {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (hK : K.ResUpTo 1 ε) (s : R) :
    UpTo s (φ.mapH 0) ↔ InjUpTo s (φ.f 0 ∘ₗ ε) ∧ ExactUpTo s (φ.f 0 ∘ₗ ε) (L.d 0) := by
  obtain ⟨hd, hi, he, -⟩ := hK
  have hLd : ∀ x, L.d 0 (φ.f 0 (ε x)) = 0 := fun x => by rw [φ.comm, hd, map_zero]
  constructor
  · rintro ⟨hI, hS⟩
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h1 : φ.mapH 0 (K.cls (ε x) (hd x)) = 0 := by
        rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd x)]
        exact resLe_cls_zero L 0 _ _ (by rw [show φ.f 0 (ε x) = 0 from hx]; exact Submodule.zero_mem _)
      have h2 := hI _ h1
      have hs' : K.d 0 (s • ε x) = 0 := by rw [map_smul, hd, smul_zero]
      rw [← resLe_cls_smul K 0 s _ _ hs'] at h2
      have h3 : s • ε x = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj K 0).2.1 _ hs').1 h2)
      rw [← map_smul] at h3
      have := hi _ h3
      rwa [one_smul] at this
    · obtain ⟨x, hx⟩ := hS (L.cls y hy)
      obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      obtain ⟨m, hm⟩ := he a ha
      rw [one_smul] at hm
      refine ⟨m, ?_⟩
      have hy' : L.d 0 (s • y) = 0 := by rw [map_smul, hy, smul_zero]
      have hfa : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hfa, ← resLe_cls_smul L 0 s y hy hy'] at hx
      have := ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ hfa hy').1 hx
      change φ.f 0 (ε m) = s • y
      rw [hm]
      exact sub_eq_zero.1 (eq_zero_of_mem_boundaries_zero _ _ this)
  · rintro ⟨hI, hE⟩
    refine ⟨fun x hx => ?_, fun y => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K 0).1 x
      have hfa : L.d 0 (φ.f 0 a) = 0 := by rw [φ.comm, ha, map_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 a ha hfa] at hx
      have h0 : φ.f 0 a = 0 := eq_zero_of_mem_boundaries_zero _ _ (((CrystallineSemistableComparison.P.cls_surj L 0).2.1 _ hfa).1 hx)
      obtain ⟨m, hm⟩ := he a ha
      rw [one_smul] at hm
      have h1 : s • m = 0 := hI m (by change φ.f 0 (ε m) = 0; rw [hm, h0])
      have hs' : K.d 0 (s • a) = 0 := by rw [map_smul, ha, smul_zero]
      rw [← resLe_cls_smul K 0 s a ha hs']
      exact resLe_cls_zero K 0 _ hs' (by rw [← hm, ← map_smul, h1, map_zero]; exact Submodule.zero_mem _)
    · obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj L 0).1 y
      obtain ⟨m, hm⟩ := hE b hb
      refine ⟨K.cls (ε m) (hd m), ?_⟩
      have hb' : L.d 0 (s • b) = 0 := by rw [map_smul, hb, smul_zero]
      rw [CrystallineSemistableComparison.P.mapH_cls φ 0 _ _ (hLd m), ← resLe_cls_smul L 0 s b hb hb']
      exact ((CrystallineSemistableComparison.P.cls_surj L 0).2.2.1 _ _ _ hb').2 (by
        rw [show φ.f 0 (ε m) = s • b from hm, sub_self]; exact Submodule.zero_mem _)

theorem resLe_cx {R : Type} [CommRing R] {K : Cx.{w} R} {L : Cx.{w'} R} (φ : Cx.Hom K L (RingHom.id R))
    {M : Type u''} [AddCommGroup M] [Module R M] (ε : M →ₗ[R] K.X 0) (hK : K.ResUpTo 1 ε) (s : R) :
    L.ResUpTo s (φ.f 0 ∘ₗ ε) ↔ ∀ n, UpTo s (φ.mapH n) := by
  have hd : ∀ x, L.d 0 ((φ.f 0 ∘ₗ ε) x) = 0 := fun x => by
    change L.d 0 (φ.f 0 (ε x)) = 0
    rw [φ.comm, hK.1, map_zero]
  constructor
  · rintro ⟨-, hi, he, hn⟩ n
    cases n with
    | zero => exact (resLe_zero φ ε hK s).2 ⟨hi, he⟩
    | succ n => exact (resLe_succ φ n (hK.2.2.2 n) s).2 (hn n)
  · intro h
    obtain ⟨hi, he⟩ := (resLe_zero φ ε hK s).1 (h 0)
    exact ⟨hd, hi, he, fun n => (resLe_succ φ n (hK.2.2.2 n) s).1 (h (n + 1))⟩

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.res_le : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] (F : C ⥤ ModuleCat.{w} R) (F' : C' ⥤ ModuleCat.{w'} R) (m : Mor F F' (RingHom.id R)) (T₀ : C) (h : Limits.IsInitial T₀) (s : R), ((cx F').ResUpTo s (aug F' fun T => (m.τ T) ∘ₗ (F.map (h.to _)).hom) ↔ ∀ n, UpTo s (m.pull n)) := by
  intro R _ C _ C' _ F F' m T₀ h s
  have e : (aug F' fun T => (m.τ T) ∘ₗ (F.map (h.to _)).hom) = m.hom.f 0 ∘ₗ aug F fun T => (F.map (h.to T)).hom := by
    apply LinearMap.ext; intro x; funext c; rfl
  rw [e]
  exact CrystallineSemistableComparison.B.resLe_cx m.hom _ (CrystallineSemistableComparison.P.initial F T₀ h) s
end

section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace CrystallineSemistableComparison.B

noncomputable def fib_init {C : Type u} [Category.{v} C] (T : C) :
    Limits.IsInitial (StructuredArrow.mk (𝟙 T) : StructuredArrow T (𝟭 C)) :=
  StructuredArrow.mkIdInitial (T := 𝟭 C) (Y := T)

theorem fib_to {C : Type u} [Category.{v} C] (T : C) (y : StructuredArrow T (𝟭 C)) :
    ((fib_init T).to y).right = y.hom := by
  have := (fib_init T).hom_ext ((fib_init T).to y) (StructuredArrow.homMk y.hom (by simp))
  exact congrArg CommaMorphism.right this

theorem fib_aug {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
    {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (T : C) :
    (aug (relF (m.G ⋙ 𝟭 C) F' T) fun x => ((relMor (𝟭 C) m T).τ x) ∘ₗ
      ((relF (𝟭 C) F T).map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj x))).hom) =
    (aug (StructuredArrow.proj T m.G ⋙ F') fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom) := by
  apply LinearMap.ext; intro a; funext c
  change m.τ _ ((F.map ((fib_init T).to ((relMor (𝟭 C) m T).G.obj (c.obj (Fin.last 0)))).right).hom a) = m.τ _ ((F.map (c.obj (Fin.last 0)).hom).hom a)
  rw [fib_to]
  rfl

end CrystallineSemistableComparison.B

theorem CrystallineSemistableComparison.B.P.fib : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R} {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (s : R), (∀ T : C, (cx (StructuredArrow.proj T m.G ⋙ F')).ResUpTo s (aug (StructuredArrow.proj T m.G ⋙ F') fun x => (m.τ x.right) ∘ₗ (F.map x.hom).hom)) → ∀ n, IsoLe (s ^ (2 * n + 3)) n m := by
  intro R _ C _ C' _ F F' m s hT n
  have key : ∀ (T : C) q, UpTo s ((relMor (𝟭 C) m T).pull q) := by
    intro T
    refine (CrystallineSemistableComparison.B.P.res_le _ _ (relMor (𝟭 C) m T) _ (CrystallineSemistableComparison.B.fib_init T) s).1 ?_
    rw [CrystallineSemistableComparison.B.fib_aug m T]
    exact hT T
  intro j hj
  have h1 := CrystallineSemistableComparison.P.rel (𝟭 C) m s j (fun i q _ => key i q)
  obtain ⟨k, rfl⟩ : ∃ k, n = j + k := ⟨n - j, by omega⟩
  have e : s ^ (2 * (j + k) + 3) = s ^ (2 * j + 3) * s ^ (2 * k) := by rw [← pow_add]; ring_nf
  rw [e]
  exact (CrystallineSemistableComparison.P.upTo_alg (m.pull j) LinearMap.id _ _).2.2.2.1 h1
end
