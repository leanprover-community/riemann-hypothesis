import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar

section
noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

section Semi

variable {R R' : Type} [Ring R] [Ring R'] (σ : R →+* R') [RingHomSurjective σ]
variable {M N X Y : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup X] [Module R' X] [AddCommGroup Y] [Module R' Y]

theorem nonempty_equiv_of_semilinear (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (g : N →ₛₗ[σ] Y)
    (hg : Function.Bijective g) (u : M ≃ₗ[R] N) : Nonempty (X ≃ₗ[R'] Y) := by
  let f' : M ≃+ X := AddEquiv.ofBijective f.toAddMonoidHom hf
  let g' : N ≃+ Y := AddEquiv.ofBijective g.toAddMonoidHom hg
  have key : ∀ x, (f'.symm.trans (u.toAddEquiv.trans g')) (f x) = g (u x) := fun x => by
    change g' (u (f'.symm (f' x))) = _
    rw [AddEquiv.symm_apply_apply]; rfl
  refine ⟨{ f'.symm.trans (u.toAddEquiv.trans g') with map_smul' := fun c x => ?_ }⟩
  obtain ⟨c, rfl⟩ := RingHomSurjective.is_surjective (σ := σ) c
  obtain ⟨x, rfl⟩ := hf.2 x
  change (f'.symm.trans (u.toAddEquiv.trans g')) (σ c • f x) = σ c • (f'.symm.trans (u.toAddEquiv.trans g')) (f x)
  rw [← map_smulₛₗ, key, key, map_smul, map_smulₛₗ]

def mapSeries (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (s : CompositionSeries (Submodule R M)) :
    CompositionSeries (Submodule R' X) where
  length := s.length
  toFun := fun i => Submodule.orderIsoMapComapOfBijective f hf (s i)
  step := fun i => (apply_covBy_apply_iff (Submodule.orderIsoMapComapOfBijective f hf)).mpr (s.step i)

theorem exists_factor_map (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (p q : Submodule R M) :
    ∃ u : (↥q ⧸ p.comap q.subtype) →ₛₗ[σ] (↥(q.map f) ⧸ (p.map f).comap (q.map f).subtype),
      Function.Bijective u := by
  let r : ↥q →ₛₗ[σ] ↥(q.map f) := (f.domRestrict q).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  refine ⟨Submodule.mapQ _ _ r fun x hx => ⟨x, hx, rfl⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, hy, hxy⟩ := (Submodule.Quotient.mk_eq_zero _).1 (show Submodule.Quotient.mk (r x) = 0 from hx)
    rw [Submodule.Quotient.mk_eq_zero]
    have : y = x := hf.1 hxy
    change (x : M) ∈ p
    exact this ▸ hy
  · intro y
    obtain ⟨⟨_, x, hx, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩

theorem sameFactors_of_semilinear (f : M →ₛₗ[σ] X) (hf : Function.Bijective f) (g : N →ₛₗ[σ] Y)
    (hg : Function.Bijective g) (h : SameFactors R M N) : SameFactors R' X Y := by
  obtain ⟨s, t, h1, h2, h3, h4, e, he⟩ := h
  refine ⟨mapSeries σ f hf s, mapSeries σ g hg t, ?_, ?_, ?_, ?_, e, fun i => ?_⟩
  · change Submodule.orderIsoMapComapOfBijective f hf s.head = ⊥
    rw [h1, map_bot]
  · change Submodule.orderIsoMapComapOfBijective f hf s.last = ⊤
    rw [h2, map_top]
  · change Submodule.orderIsoMapComapOfBijective g hg t.head = ⊥
    rw [h3, map_bot]
  · change Submodule.orderIsoMapComapOfBijective g hg t.last = ⊤
    rw [h4, map_top]
  · obtain ⟨u⟩ := he i
    obtain ⟨a, ha⟩ := exists_factor_map σ f hf (s (Fin.castSucc (n := s.length) i)) (s (Fin.succ (n := s.length) i))
    obtain ⟨b, hb⟩ := exists_factor_map σ g hg (t (e i).castSucc) (t (e i).succ)
    exact nonempty_equiv_of_semilinear σ a ha b hb u

end Semi

section Res

variable {O k G : Type} [CommRing O] [Field k] [Algebra O k] [Group G]

def twHom (k : Type) [Field k] [Algebra O k] (θ : G →* Oˣ) : MonoidAlgebra O G →ₐ[O] MonoidAlgebra k G :=
  MonoidAlgebra.lift _ _ _
    { toFun := fun g => MonoidAlgebra.single g (algebraMap O k ((θ g)⁻¹ : Oˣ))
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := fun g h => by simp [MonoidAlgebra.single_mul_single, mul_comm] }

theorem twHom_single (θ : G →* Oˣ) (g : G) (a : O) :
    twHom k θ (MonoidAlgebra.single g a) = MonoidAlgebra.single g (algebraMap O k (a * ((θ g)⁻¹ : Oˣ))) := by
  rw [twHom, MonoidAlgebra.lift_single]
  change a • MonoidAlgebra.single g (algebraMap O k ((θ g)⁻¹ : Oˣ)) = _
  rw [MonoidAlgebra.smul_single, map_mul, Algebra.smul_def]

theorem twHom_surjective (hs : Function.Surjective (algebraMap O k)) (θ : G →* Oˣ) :
    Function.Surjective (twHom k θ) := by
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
  | single g c =>
    obtain ⟨a, rfl⟩ := hs c
    exact ⟨MonoidAlgebra.single g (a * θ g), by rw [twHom_single]; simp [mul_assoc]⟩

variable {M N X Y : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup X] [Module k X] [Module O X] [IsScalarTower O k X]
  [AddCommGroup Y] [Module k Y] [Module O Y] [IsScalarTower O k Y]

def twSemi (θ : G →* Oˣ) (π : Representation O G M) (α : Representation k G X) (e : M →ₗ[O] X)
    (he : ∀ g x, e (twistRep π θ g x) = α g (e x)) :
    π.asModule →ₛₗ[(twHom k θ : MonoidAlgebra O G →+* MonoidAlgebra k G)] α.asModule where
  toFun x := α.asModuleEquiv.symm (e (π.asModuleEquiv x))
  map_add' x y := by simp only [map_add]
  map_smul' r x := by
    apply α.asModuleEquiv.injective
    rw [Representation.asModuleEquiv_map_smul, Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | single g c =>
      rw [RingHom.coe_coe, twHom_single, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single,
        LinearMap.smul_apply, LinearMap.smul_apply, ← he, twistRep_apply, algebraMap_smul, map_smul, map_smul,
        smul_smul]
      simp

theorem sameSS_twist_residue (hs : Function.Surjective (algebraMap O k)) (θ : G →* Oˣ)
    {π : Representation O G M} {π' : Representation O G N} {α : Representation k G X} {α' : Representation k G Y}
    (e : M ≃ₗ[O] X) (he : ∀ g x, e (twistRep π θ g x) = α g (e x))
    (e' : N ≃ₗ[O] Y) (he' : ∀ g x, e' (twistRep π' θ g x) = α' g (e' x)) (h : SameSS π π') : SameSS α α' := by
  have : RingHomSurjective (twHom k θ : MonoidAlgebra O G →+* MonoidAlgebra k G) := ⟨twHom_surjective hs θ⟩
  refine sameFactors_of_semilinear _ (twSemi θ π α e.toLinearMap he) ?_ (twSemi θ π' α' e'.toLinearMap he') ?_ h
  · exact α.asModuleEquiv.symm.bijective.comp (e.bijective.comp π.asModuleEquiv.bijective)
  · exact α'.asModuleEquiv.symm.bijective.comp (e'.bijective.comp π'.asModuleEquiv.bijective)

theorem exists_descend {lam : O} (hs : Function.Surjective (algebraMap O k)) (h0 : algebraMap O k lam = 0)
    (q : M →ₗ[O] X) (hq : Function.Surjective q) (hk : KerIs lam q) (f : M →ₗ[O] Y) :
    ∃ a : X →ₗ[k] Y, ∀ x, a (q x) = f x := by
  have hle : LinearMap.ker q ≤ LinearMap.ker f := fun x hx => by
    obtain ⟨y, rfl⟩ := (hk x).1 hx
    rw [LinearMap.mem_ker, map_smul, ← algebraMap_smul k, h0, zero_smul]
  let a : X →ₗ[O] Y := (Submodule.liftQ _ f hle).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  refine ⟨a.extendScalarsOfSurjective hs, fun x => ?_⟩
  change Submodule.liftQ _ f hle ((q.quotKerEquivOfSurjective hq).symm (q x)) = _
  have : (q.quotKerEquivOfSurjective hq).symm (q x) = Submodule.Quotient.mk x := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem exists_reduction {lam : O} (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) [Module.Free O M] [Module.Finite O M]
    (π : Representation O G M) : ∃ (A : Ob k G) (q : M →ₗ[O] (Fin A.m → k)), A.m = Module.finrank O M ∧
      Function.Surjective q ∧ KerIs lam q ∧ ∀ g x, q (π g x) = A.ρ g (q x) := by
  have : Nontrivial O := (algebraMap O k).domain_nontrivial
  let b := (Module.finBasis O M).equivFun
  let q : M →ₗ[O] (Fin (Module.finrank O M) → k) := ((Algebra.linearMap O k).compLeft _).comp b.toLinearMap
  have hq' : ∀ x j, q x j = algebraMap O k (b x j) := fun _ _ => rfl
  have hq : Function.Surjective q := fun y => by
    choose x hx using fun j => hs (y j)
    exact ⟨b.symm x, funext fun j => by rw [hq', LinearEquiv.apply_symm_apply, hx]⟩
  have hK : KerIs lam q := fun x => by
    constructor
    · intro h
      choose y hy using fun j => (hk (b x j)).1 (congrFun h j)
      refine ⟨b.symm y, b.injective ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact funext hy
    · rintro ⟨y, rfl⟩
      rw [map_smul, ← algebraMap_smul k, (hk lam).2 dvd_rfl, zero_smul]
  choose a ha using fun g => exists_descend hs ((hk lam).2 dvd_rfl) q hq hK (q.comp (π g))
  refine ⟨⟨_, { toFun := a, map_one' := ?_, map_mul' := fun g h => ?_ }⟩, q, rfl, hq, hK, fun g x => (ha g x).symm⟩
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hq y
    rw [ha]; simp
  · refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hq y
    have ha' : ∀ g x, a g (q x) = q (π g x) := ha
    change a (g * h) (q x) = a g (a h (q x))
    rw [ha', ha', ha', map_mul, Module.End.mul_apply]

end Res

section Fun

variable {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l}

theorem pre_push_sup (F : DFun R n G) (A B C : Ob k G) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hA : F.Obj A) (hB : F.Obj B) (hC : F.Obj C) (ha : IsHom A C a)
    (hb : IsHom B C b) (hab : Function.Bijective (a.coprod b)) (N : Lats k n A.m) (N' : Lats k n B.m) :
    F.pre A C a (fun i => F.push A C a N i ⊔ F.push B C b N' i) = N := by
  let e := LinearEquiv.ofBijective (a.coprod b) hab
  let p : (Fin C.m → k) →ₗ[k] (Fin A.m → k) := (LinearMap.fst k _ _).comp e.symm.toLinearMap
  have hp : ∀ x y, p (a x + b y) = x := fun x y => congrArg Prod.fst (e.symm_apply_apply (x, y))
  have hpH : IsHom C A p := fun g z => by
    obtain ⟨⟨x, y⟩, rfl⟩ := hab.2 z
    rw [LinearMap.coprod_apply, map_add, ← ha, ← hb, hp, hp]
  have h1 : p ∘ₗ a = LinearMap.id := LinearMap.ext fun x => by simpa using hp x 0
  have h2 : p ∘ₗ b = (0 : k) • (p ∘ₗ b) := LinearMap.ext fun y => by simpa using hp 0 y
  have hpb : IsHom B A (p ∘ₗ b) := fun g x => by
    change p (b _) = A.ρ g (p (b x))
    rw [hb, hpH]
  have h3 : ∀ i x, F.map C A p i (F.map A C a i x) = x := fun i x => by
    rw [← LinearMap.comp_apply, ← F.map_comp A C A a p hA hC hA ha hpH, h1, F.map_id A hA, LinearMap.id_apply]
  have h4 : ∀ i x, F.map C A p i (F.map B C b i x) = 0 := fun i x => by
    rw [← LinearMap.comp_apply, ← F.map_comp B C A b p hB hC hA hb hpH, h2, F.map_smul B A _ _ hB hA hpb, zero_smul]
  funext i
  ext x
  constructor
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, _, ⟨z, -, rfl⟩, h⟩ := Submodule.mem_sup.1 (show F.map A C a i x ∈ _ from hx)
    have h' := congrArg (F.map C A p i) h
    change F.map C A p i (F.map A C a i y + F.map B C b i z) = _ at h'
    rw [map_add, h3, h3, h4, add_zero] at h'
    exact h' ▸ hy
  · intro hx
    exact Submodule.mem_sup_left ⟨x, hx, rfl⟩

def IsTrace (F : DFun R n G) (A : Ob k G) (N : Lats k n A.m) (C : Ob k G) (L : Lats k n C.m) : Prop :=
  ∃ a, IsHom A C a ∧ Function.Injective a ∧ N = F.pre A C a L

theorem IsTrace.refl (F : DFun R n G) (A : Ob k G) (hA : F.Obj A) (N : Lats k n A.m) : IsTrace F A N A N :=
  ⟨LinearMap.id, fun _ _ => rfl, Function.injective_id, by
    funext i; ext x
    change _ ↔ F.map A A LinearMap.id i x ∈ N i
    rw [F.map_id A hA, LinearMap.id_apply]⟩

theorem IsTrace.trans {F : DFun R n G} {A B C : Ob k G} (hC : F.Obj C) {N : Lats k n A.m} {M : Lats k n B.m}
    {L : Lats k n C.m} (h : IsTrace F A N B M) (h' : IsTrace F B M C L) : IsTrace F A N C L := by
  obtain ⟨a, ha, hi, rfl⟩ := h
  obtain ⟨b, hb, hj, rfl⟩ := h'
  have hB := F.obj_sub B C b hb hj hC
  have hA := F.obj_sub A B a ha hi hB
  refine ⟨b ∘ₗ a, fun g x => by rw [LinearMap.comp_apply, LinearMap.comp_apply, ha, hb], hj.comp hi, ?_⟩
  funext i; ext x
  change _ ↔ F.map A C (b ∘ₗ a) i x ∈ L i
  rw [F.map_comp A B C a b hA hB hC ha hb]
  rfl

theorem isTrace_sum (F : DFun R n G) (A B C : Ob k G) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hC : F.Obj C) (ha : IsHom A C a)
    (hb : IsHom B C b) (hab : Function.Bijective (a.coprod b)) (N : Lats k n A.m) (N' : Lats k n B.m) :
    IsTrace F A N C (fun i => F.push A C a N i ⊔ F.push B C b N' i) ∧
      IsTrace F B N' C (fun i => F.push A C a N i ⊔ F.push B C b N' i) := by
  have hi : Function.Injective a := fun x y h => congrArg Prod.fst (hab.1 (a₁ := (x, 0)) (a₂ := (y, 0)) (by simpa))
  have hj : Function.Injective b := fun x y h => congrArg Prod.snd (hab.1 (a₁ := (0, x)) (a₂ := (0, y)) (by simpa))
  have hA := F.obj_sub A C a ha hi hC
  have hB := F.obj_sub B C b hb hj hC
  refine ⟨⟨a, ha, hi, (pre_push_sup F A B C a b hA hB hC ha hb hab N N').symm⟩, b, hb, hj, ?_⟩
  have hba : Function.Bijective (b.coprod a) := by
    have : ⇑(b.coprod a) = (a.coprod b) ∘ Prod.swap := funext fun x => by simp [add_comm]
    rw [this]
    exact hab.comp Prod.swap_bijective
  simp only [sup_comm (F.push A C a N _)]
  exact (pre_push_sup F B A C b a hB hA hC hb ha hba N' N).symm

theorem IsTrace.isModel {F : DFun R n G} {Base : ∀ A : Ob k G, Lats k n A.m → Prop} {A C : Ob k G}
    (hC : F.Obj C) {N : Lats k n A.m} {L : Lats k n C.m} (h : IsTrace F A N C L) (hb : Base C L) :
    IsModel F Base A N := by
  obtain ⟨a, ha, hi, rfl⟩ := h
  refine ⟨C, L, A, a, LinearMap.id, hb, ha, hi, fun _ _ => rfl, Function.surjective_id, ?_⟩
  funext i
  change _ = Submodule.map _ _
  rw [F.map_id A (F.obj_sub A C a ha hi hC)]
  exact (Submodule.map_id _).symm

theorem eq_span_unit [Fact l.Prime] [CharP k l] [NeZero n] (F : DFun R n G) (ψ : G →* kˣ) (hψ : ψ = 1)
    (N : Lats k n 1) (hN : ∀ i, IsLat (N i)) (h : ∀ i, pull ((F.D (chr ψ)).φ i) (N (i - 1)) = sh 0 (N i)) :
    ∀ i, N i = Submodule.span k⟦X⟧ {F.unit i} := by
  subst hψ
  let M : Lats k n 1 := fun i => Submodule.span k⟦X⟧ {F.unit i}
  have hM : ∀ i, IsLat (M i) := fun i => by
    refine ⟨Submodule.fg_span_singleton _, eq_top_iff.2 fun x _ => ?_⟩
    have h1 : F.unit i ∈ Submodule.span k⸨X⸩ (M i : Set (Vc k 1)) :=
      Submodule.subset_span (Submodule.mem_span_singleton_self _)
    have h0 : F.unit i 0 ≠ 0 := fun h0 => F.unit_ne i (funext fun j => by rw [Subsingleton.elim j 0]; exact h0)
    have h2 : x = (x 0 / F.unit i 0) • F.unit i := funext fun j => by
      rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hM' : ∀ i, pull ((F.D (chr 1)).φ i) (M (i - 1)) = M i := fun i => by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
      obtain ⟨d, hd⟩ := R.φ_int c
      refine Submodule.mem_span_singleton.2 ⟨d, ?_⟩
      rw [← algebraMap_smul k⸨X⸩ c, (F.D (chr 1)).φ_semi i, F.unit_φ, ← algebraMap_smul k⸨X⸩ d]
      exact congrArg (· • F.unit i) hd.symm
    · refine Submodule.span_le.2 ?_
      rintro _ rfl
      exact Submodule.subset_span ⟨_, Submodule.mem_span_singleton_self _, F.unit_φ i⟩
  have c1 : CondAB (F.D (chr 1)).φ (fun _ => 0) (fun _ => ((0 : ℕ) : ℤ) - 0) N := fun i => by
    rw [h i]; simp
  have c2 : CondAB (F.D (chr 1)).φ (fun _ => 0) (fun _ => ((0 : ℕ) : ℤ) - 0) M := fun i => by
    rw [hM' i]; simp [sh_zero_eq]
  intro i
  have hs : sg l (fun _ : ZMod n => 0) i = 0 := by simp [sg]
  have d1 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr 1)) (fun _ => 0) (fun _ => 0) N M hN hM c1 c2 i
  have d2 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr 1)) (fun _ => 0) (fun _ => 0) M N hM hN c2 c1 i
  rw [hs, Nat.cast_zero, sh_zero_eq] at d1 d2
  exact le_antisymm d1 d2

theorem resCount_nsmul_map (μ : ℕ) (U : Multiset ℤ) (w : ℤ) (x : k) :
    resCount ((μ • U).map (· + -w)) 0 x = μ * resCount U w x := by
  classical
  simp only [resCount, ← Multiset.countP_eq_card_filter, Multiset.countP_map, Multiset.filter_nsmul,
    Multiset.card_nsmul, sub_zero, ← sub_eq_add_neg]

end Fun

section Arith

variable {n r : ℕ} (D : TopData n r)

theorem w_range (i : ZMod n) : 1 ≤ D.w i ∧ D.w i ≤ (D.h i : ℤ) - 1 :=
  D.range i _ (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by have := D.one_le_letterBlockLength; omega⟩)))

theorem eq_of_dvd {l : ℕ} (h1 : D.T1 l) (h3 : D.T3 l) (i : ZMod n) (hi : D.ty i = LType.Bd) (u : ℤ)
    (hu : u ∈ D.Ut i) (a : ℕ) (ha : (a : ℤ) ≤ D.wst i) (hd : (l : ℤ) ∣ (a : ℤ) - (u + -D.w i)) :
    (a : ℤ) = u + -D.w i := by
  have hw := D.lowBd i hi (D.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by have := D.one_le_letterBlockLength; omega⟩)))
  have hl := h1 i
  rw [TopData.wst] at ha
  have low : u ∈ D.lows i + block (D.w i) D.t → (a : ℤ) = u + -D.w i := fun h => by
    have := D.lowBd i hi u h
    have := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; omega)
    omega
  rcases Multiset.mem_add.1 hu with hu | hu
  · rcases Multiset.mem_add.1 hu with hu | hu
    · exact low (Multiset.mem_add.2 (Or.inl hu))
    · refine absurd ?_ (h3 i u hu ((D.h i : ℤ) - D.w i - a) (by omega) (by omega))
      rw [TopData.cloudRes, hi]
      refine (Int.modEq_iff_dvd.2 ?_).symm
      convert hd using 1
      ring
  · exact low (Multiset.mem_add.2 (Or.inr hu))

end Arith

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing O] [Algebra O LL] [TopologicalSpace LL]

def piLattice {μ : ℕ} (T : LocLat G Qp LL O) (F : Fin μ → LocLat G Qp LL O) (e : T.V ≃ₗ[LL] (∀ j, (F j).V))
    (he : ∀ g x j, e (T.ρ g x) j = (F j).ρ g (e x j)) :
    {L : Lattice (O := O) T.ρ // ∃ u : ↥L.T ≃ₗ[O] (∀ j, ↥(F j).L.T), ∀ x j, (u x j : (F j).V) = e x j} := by
  let N : Submodule O T.V := (Submodule.pi Set.univ fun j => (F j).L.T).comap (e.restrictScalars O).toLinearMap
  let u : ↥N ≃ₗ[O] (∀ j, ↥(F j).L.T) :=
    { toFun := fun x j => ⟨e x j, x.2 j trivial⟩
      invFun := fun y => ⟨e.symm fun j => y j, fun j _ => by
        change e (e.symm _) j ∈ _
        rw [LinearEquiv.apply_symm_apply]; exact (y j).2⟩
      map_add' := fun x y => funext fun j => Subtype.ext (congrFun (map_add e x.1 y.1) j)
      map_smul' := fun c x => funext fun j => Subtype.ext (congrFun (map_smul (e.restrictScalars O) c x.1) j)
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := fun y => funext fun j => Subtype.ext (congrFun (e.apply_symm_apply fun j => y j) j) }
  have hfin : ∀ j, Module.Finite O ↥(F j).L.T := fun j => StdAdm.finite_lat (F j)
  have hfree : ∀ j, Module.Free O ↥(F j).L.T := fun j => (F j).L.free
  refine ⟨{ T := N, stable := fun g x hx j _ => ?_, fg := ?_, free := Module.Free.of_equiv u.symm, span := ?_ },
    u, fun _ _ => rfl⟩
  · change e (T.ρ g x) j ∈ _
    rw [he]
    exact (F j).L.stable g _ (hx j trivial)
  · exact Module.Finite.iff_fg.mp (Module.Finite.equiv u.symm)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := e.symm.surjective x
    rw [← Finset.univ_sum_single y, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have hy : y j ∈ Submodule.span LL ((F j).L.T : Set (F j).V) := by rw [(F j).L.span]; trivial
    have h1 := Submodule.mem_map_of_mem
      (f := e.symm.toLinearMap.comp (LinearMap.single LL (fun j => (F j).V) j)) hy
    rw [Submodule.map_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ha, rfl⟩ i _
    change e (e.symm (Pi.single j a)) i ∈ _
    rw [LinearEquiv.apply_symm_apply]
    by_cases h : i = j
    · subst h; rw [Pi.single_eq_same]; exact ha
    · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

def piLoc [IsTopologicalRing LL] {μ : ℕ} (F : Fin μ → LocLat G Qp LL O) : LocLat G Qp LL O where
  V := ∀ j, (F j).V
  ρ := piRep fun j => (F j).ρ
  cont := fun x => continuous_pi fun j => (F j).cont (x j)
  L :=
    { T := Submodule.pi Set.univ fun j => (F j).L.T
      stable := fun g x hx j _ => (F j).L.stable g _ (hx j trivial)
      fg := Submodule.fg_pi fun j => (F j).L.fg
      free := by
        have hfree : ∀ j, Module.Free O ↥(F j).L.T := fun j => (F j).L.free
        let u : ↥(Submodule.pi Set.univ fun j => (F j).L.T) ≃ₗ[O] (∀ j, ↥(F j).L.T) :=
          { toFun := fun x j => ⟨x.1 j, x.2 j trivial⟩
            invFun := fun y => ⟨fun j => y j, fun j _ => (y j).2⟩
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        exact Module.Free.of_equiv u.symm
      span := by
        rw [eq_top_iff]
        intro y _
        rw [← Finset.univ_sum_single y]
        refine Submodule.sum_mem _ fun j _ => ?_
        have hy : y j ∈ Submodule.span LL ((F j).L.T : Set (F j).V) := by rw [(F j).L.span]; trivial
        have h1 := Submodule.mem_map_of_mem (f := LinearMap.single LL (fun j => (F j).V) j) hy
        rw [Submodule.map_span] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨a, ha, rfl⟩ i _
        change Pi.single (M := fun j => (F j).V) j a i ∈ _
        by_cases h : i = j
        · subst h; rw [Pi.single_eq_same]; exact ha
        · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _ }

variable {k : Type} [Field k] [Algebra O k]

theorem exists_sum_reduction {lam : O} (T T' Z : LocLat G Qp LL O) (u : ↥Z.L.T ≃ₗ[O] (↥T.L.T × ↥T'.L.T))
    (hu : ∀ g x, u (latRep Z.L g x) = (latRep T.L g (u x).1, latRep T'.L g (u x).2))
    (A B : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (q' : ↥T'.L.T →ₗ[O] (Fin B.m → k))
    (h : Onto T A q) (hk : KerIs lam q) (h' : Onto T' B q') (hk' : KerIs lam q') :
    ∃ (C : Ob k G) (r : ↥Z.L.T →ₗ[O] (Fin C.m → k)) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
      (b : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), Onto Z C r ∧ KerIs lam r ∧ IsHom A C a ∧ IsHom B C b ∧
      Function.Bijective (a.coprod b) ∧ ∀ z, r z = a (q (u z).1) + b (q' (u z).2) := by
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.prod B.ρ)
  refine ⟨C, (e.restrictScalars O).toLinearMap ∘ₗ (q.prodMap q') ∘ₗ u.toLinearMap,
    e.toLinearMap ∘ₗ LinearMap.inl k _ _, e.toLinearMap ∘ₗ LinearMap.inr k _ _,
    ⟨e.surjective.comp ((h.1.prodMap h'.1).comp u.surjective), fun g x => ?_⟩, fun x => ?_, fun g x => ?_,
    fun g x => ?_, ?_, fun z => ?_⟩
  · change e (q (u _).1, q' (u _).2) = C.ρ g (e (q (u x).1, q' (u x).2))
    rw [hu, h.2, h'.2, ← he]
    rfl
  · change e (q (u x).1, q' (u x).2) = 0 ↔ _
    rw [e.map_eq_zero_iff, Prod.mk_eq_zero, hk, hk']
    constructor
    · rintro ⟨⟨a, ha⟩, b, hb⟩
      refine ⟨u.symm (a, b), u.injective ?_⟩
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact Prod.ext ha hb
    · rintro ⟨y, rfl⟩
      rw [map_smul]
      exact ⟨⟨_, rfl⟩, _, rfl⟩
  · change e (A.ρ g x, 0) = C.ρ g (e (x, 0))
    rw [← he]
    exact congrArg e (Prod.ext rfl (map_zero (B.ρ g)).symm)
  · change e (0, B.ρ g x) = C.ρ g (e (0, x))
    rw [← he]
    exact congrArg e (Prod.ext (map_zero (A.ρ g)).symm rfl)
  · have : ⇑((e.toLinearMap ∘ₗ LinearMap.inl k _ _).coprod (e.toLinearMap ∘ₗ LinearMap.inr k _ _)) = e :=
      funext fun x => by simp [← map_add]
    rw [this]
    exact e.bijective
  · change e (q (u z).1, q' (u z).2) = e (q (u z).1, 0) + e (0, q' (u z).2)
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]

theorem exists_char_reduction {lam : O} (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (T : LocLat G Qp LL O) (u : O ≃ₗ[O] ↥T.L.T) (χ : G →* Oˣ)
    (hu : ∀ g a, latRep T.L g (u a) = (χ g : O) • u a) (ψ : G →* kˣ) (hψ : ∀ g, (ψ g : k) = algebraMap O k (χ g)) :
    ∃ q : ↥T.L.T →ₗ[O] (Fin 1 → k), Onto T (chr ψ) q ∧ KerIs lam q := by
  let q : ↥T.L.T →ₗ[O] (Fin 1 → k) := (LinearMap.pi fun _ => Algebra.linearMap O k) ∘ₗ u.symm.toLinearMap
  have hq : ∀ a j, q (u a) j = algebraMap O k a := fun a j => congrArg (algebraMap O k) (u.symm_apply_apply a)
  refine ⟨q, ⟨fun y => ?_, fun g x => ?_⟩, fun x => ?_⟩
  · obtain ⟨a, ha⟩ := hs (y 0)
    exact ⟨u a, funext fun j => by rw [hq, ha, Subsingleton.elim j 0]⟩
  · obtain ⟨a, rfl⟩ := u.surjective x
    rw [hu, map_smul, ← algebraMap_smul k, ← hψ]
    rfl
  · obtain ⟨a, rfl⟩ := u.surjective x
    constructor
    · intro h
      obtain ⟨b, rfl⟩ := (hk a).1 ((hq a 0).symm.trans (congrFun h 0))
      exact ⟨u b, map_smul u lam b⟩
    · rintro ⟨y, hy⟩
      rw [hy, map_smul, ← algebraMap_smul k, (hk lam).2 dvd_rfl, zero_smul]

theorem kerIs_iff {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] {lam : O}
    {q : M →ₗ[O] N} (h : KerIs lam q) (x : M) : q x = 0 ↔ x ∈ lam • (⊤ : Submodule O M) := by
  rw [h x, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, trivial, hy.symm⟩, fun ⟨y, _, hy⟩ => ⟨y, hy.symm⟩⟩

theorem exists_quot_equiv {M N : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] {lam : O}
    (q : M →ₗ[O] N) (hq : Function.Surjective q) (h : KerIs lam q) :
    ∃ e : QuotSMulTop lam M ≃ₗ[O] N, ∀ x, e (Submodule.Quotient.mk x) = q x := by
  have hker : lam • (⊤ : Submodule O M) = LinearMap.ker q := by
    ext x; rw [LinearMap.mem_ker, kerIs_iff h]
  exact ⟨(Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hq), fun _ => rfl⟩

theorem exists_ref_equiv (Γ : GalData G Qp LL O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (A : Ob k G) (q : ↥Γ.T₀.L.T →ₗ[O] (Fin A.m → k))
    (hq : Function.Surjective q) (hK : KerIs Γ.lam q) (hg : ∀ g x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ g x) = A.ρ g (q x))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) (t : ℕ) :
    ∃ e : (QuotSMulTop Γ.lam ↥Γ.T₀.L.T × (Fin t → QuotSMulTop Γ.lam O)) ≃ₗ[O]
      ((Fin A.m → k) × (Fin t → (Fin 1 → k))),
      ∀ g x, e (twistRep (Γ.refRep t) Γ.χ₁⁻¹ g x) = refSum A ω t g (e x) := by
  obtain ⟨e₀, he₀⟩ := exists_quot_equiv q hq hK
  let q₁ : O →ₗ[O] (Fin 1 → k) := LinearMap.pi fun _ => Algebra.linearMap O k
  have hq₁ : Function.Surjective q₁ := fun y => by
    obtain ⟨a, ha⟩ := hs (y 0)
    exact ⟨a, funext fun j => by rw [Subsingleton.elim j 0]; exact ha⟩
  have hK₁ : KerIs Γ.lam q₁ := fun x =>
    ⟨fun h => (hk x).1 (congrFun h 0), fun h => funext fun _ => (hk x).2 h⟩
  obtain ⟨e₁, he₁⟩ := exists_quot_equiv q₁ hq₁ hK₁
  have hω' : ω = (Units.map (algebraMap O k : O →* k)).comp Γ.ε := MonoidHom.ext fun g => Units.ext (hω g)
  refine ⟨e₀.prodCongr (LinearEquiv.piCongrRight fun _ => e₁), fun g x => Prod.ext ?_ (funext fun c => ?_)⟩
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ x.1
    change e₀ (((Γ.χ₁⁻¹ g : Oˣ) : O) • modRep Γ.W₀ Γ.lam g x.1) = A.ρ g (e₀ x.1)
    rw [← hy, he₀, ← hg]
    exact he₀ _
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.2 c)
    change e₁ (((Γ.χ₁⁻¹ g : Oˣ) : O) • modRep (Γ.Wchi (c.val + 1)) Γ.lam g (x.2 c)) =
      ((ω ^ (-(c.val : ℤ))) g : k) • e₁ (x.2 c)
    rw [← hy, he₁, modRep_mk, map_smul, he₁]
    funext j
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • algebraMap O k (((Γ.chi (c.val + 1) g : Oˣ) : O) * y) =
      ((ω ^ (-(c.val : ℤ))) g : k) * algebraMap O k y
    rw [Algebra.smul_def, ← map_mul, ← mul_assoc, ← Units.val_mul, map_mul, hω']
    congr 1
    simp [GalData.chi]

end Lat

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O}

theorem crysWith_zero {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Subsingleton V] (ρ : Representation LL G V) : CrysWith PD emb ρ (fun _ => 0) := by
  refine ⟨?_, fun i τ _ a => ?_⟩
  · rw [IsCrys, Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := V), mul_zero]
  · rw [multV, Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
    simp

theorem crysWith_pi [IsTopologicalRing LL] (hsum : StdAdm.SumRule PD emb O) {U : ZMod n → Multiset ℤ} :
    ∀ (μ : ℕ) (T : LocLat G Qp LL O) (F : Fin μ → LocLat G Qp LL O) (e : T.V ≃ₗ[LL] (∀ j, (F j).V)),
      (∀ g x j, e (T.ρ g x) j = (F j).ρ g (e x j)) → (∀ j, CrysWith PD emb (F j).ρ U) →
      CrysWith PD emb T.ρ (fun i => μ • U i)
  | 0, T, F, e, _, _ => by
    have : Subsingleton T.V := e.toEquiv.subsingleton
    simpa using crysWith_zero T.ρ
  | μ + 1, T, F, e, he, hF => by
    have ih := crysWith_pi hsum μ (piLoc fun j => F j.succ) (fun j => F j.succ) (LinearEquiv.refl _ _)
      (fun _ _ _ => rfl) fun j => hF _
    have h := hsum (F 0) (piLoc fun j => F j.succ) T _ _
      (e.trans (Fin.consLinearEquiv LL fun j => (F j).V).symm)
      (fun g x => Prod.ext (he g x 0) (funext fun j => he g x j.succ)) (hF 0) ih
    simpa only [succ_nsmul'] using h

theorem sumFull_crys [IsTopologicalRing LL] (hsum : StdAdm.SumRule PD emb O) {t μ : ℕ} {U : ZMod n → Multiset ℤ}
    {T : LocLat G Qp LL O} (h : SumFull PD emb Γ t U μ T) : CrysWith PD emb T.ρ (fun i => μ • U i) := by
  obtain ⟨F, hF, e, he⟩ := h
  exact crysWith_pi hsum μ T F e he fun j => (hF j).1

theorem sumFull_sameSS [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hlam : Irreducible Γ.lam)
    {t μ : ℕ} {U : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (h : SumFull PD emb Γ t U μ T) :
    SameSS (modRep (latRep T.L) Γ.lam) (piRep fun _ : Fin μ => Γ.refRep t) := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨L, u, hu⟩ := piLattice T F e he
  let p : ↥L.T →ₗ[O] (∀ j, QuotSMulTop Γ.lam ↥(F j).L.T) :=
    (LinearMap.pi fun j => (Submodule.mkQ _).comp (LinearMap.proj j)).comp u.toLinearMap
  have hp : ∀ x j, p x j = Submodule.Quotient.mk (u x j) := fun _ _ => rfl
  obtain ⟨f, hf⟩ := StdAdm.exists_modRep_equiv (latRep L) (piRep fun j => modRep (latRep (F j).L) Γ.lam) Γ.lam p
    (fun y => by
      choose x hx using fun j => Submodule.Quotient.mk_surjective _ (y j)
      exact ⟨u.symm x, funext fun j => by rw [hp, LinearEquiv.apply_symm_apply, hx]⟩)
    (fun x => by
      simp only [funext_iff, hp, Pi.zero_apply, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
      constructor
      · intro h
        choose b hb using h
        refine ⟨u.symm b, u.injective ?_⟩
        rw [map_smul, LinearEquiv.apply_symm_apply]
        exact funext hb
      · rintro ⟨y, rfl⟩ j
        rw [map_smul]
        exact ⟨_, rfl⟩)
    (fun g x => funext fun j => by
      rw [hp, piRep_apply, hp, modRep_mk]
      congr 1
      apply Subtype.ext
      rw [hu, latRep_apply, latRep_apply, hu, he])
  exact ((reduction_sameSS_of_lattices T.ρ T.L L Γ.lam hlam).congr_right f hf).trans
    (SameSS.piRep fun j => (hF j).2 (F j).L)

theorem exists_sum_ind [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hsum : StdAdm.SumRule PD emb O) {U : ZMod n → Multiset ℤ} {w : ZMod n → ℤ} (h0 : CrysWith PD emb Γ.T₀.ρ U)
    (hχ : ∀ c : ℕ, IsCrysChar PD emb (Γ.chi (c + 1)) (fun i => w i + c)) (Q : ℕ → LocLat G Qp LL O → Prop)
    (hQ0 : Q 0 Γ.T₀) (hQ : ∀ (k : ℕ) T, CrysWith PD emb T.ρ (fun i => U i + block (w i) k) → Q k T →
      Q (k + 1) (AdmClosure.prodLoc T (charLat Qp hinj _ (hχ k).1))) (k : ℕ) :
    ∃ (T : LocLat G Qp LL O) (e : ↥T.L.T ≃ₗ[O] (↥Γ.T₀.L.T × (Fin k → O))),
      CrysWith PD emb T.ρ (fun i => U i + block (w i) k) ∧ Q k T ∧
      ∀ g x, e (latRep T.L g x) = (Γ.W₀ g (e x).1, fun c : Fin k => Γ.Wchi (c.val + 1) g ((e x).2 c)) := by
  induction k with
  | zero =>
    refine ⟨Γ.T₀, (LinearEquiv.prodUnique).symm, ?_, hQ0, fun g x => Prod.ext rfl (Subsingleton.elim _ _)⟩
    simpa [block] using h0
  | succ k ih =>
    obtain ⟨T, e, hT, hq, he⟩ := ih
    obtain ⟨e₁, -, he₁⟩ := charLattice_equiv hinj (Γ.chi (k + 1))
    let C : LocLat G Qp LL O := charLat Qp hinj _ (hχ k).1
    let e₁' : O ≃ₗ[O] ↥C.L.T := e₁
    have he₁' : ∀ g y, e₁'.symm (latRep C.L g y) = Γ.Wchi (k + 1) g (e₁'.symm y) := by
      intro g y
      obtain ⟨a, rfl⟩ := e₁'.surjective y
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_apply]
      exact (he₁ g a).symm
    let s : ((↥Γ.T₀.L.T × (Fin k → O)) × O) ≃ₗ[O] (↥Γ.T₀.L.T × (Fin (k + 1) → O)) :=
      { toFun := fun x => (x.1.1, Fin.snoc (α := fun _ => O) x.1.2 x.2)
        invFun := fun y => ((y.1, Fin.init y.2), y.2 (Fin.last k))
        map_add' := fun a b => Prod.ext rfl (by
          funext c; refine Fin.lastCases ?_ (fun c => ?_) c <;> simp)
        map_smul' := fun a b => Prod.ext rfl (by
          funext c; refine Fin.lastCases ?_ (fun c => ?_) c <;> simp)
        left_inv := fun x => by simp
        right_inv := fun y => by simp }
    let v : ↥(AdmClosure.prodLoc T C).L.T ≃ₗ[O] (↥T.L.T × ↥C.L.T) := StdAdm.prodSubEquiv T.L.T C.L.T
    refine ⟨AdmClosure.prodLoc T C, v.trans ((e.prodCongr e₁'.symm).trans s), ?_, hQ k T hT hq, fun g x => ?_⟩
    · have h := hsum T C (AdmClosure.prodLoc T C) _ _ (LinearEquiv.refl _ _) (fun _ _ => rfl) hT (hχ k).2
      simpa only [StdAdm.block_succ, add_assoc] using h
    · change s (e (latRep T.L g (v x).1), e₁'.symm (latRep C.L g (v x).2)) =
        (Γ.W₀ g (e (v x).1).1, fun c : Fin (k + 1) => Γ.Wchi (c.val + 1) g
          (Fin.snoc (α := fun _ => O) (e (v x).1).2 (e₁'.symm (v x).2) c))
      rw [he, he₁']
      refine Prod.ext rfl ?_
      funext c
      change Fin.snoc (α := fun _ => O) _ _ c = _
      refine Fin.lastCases ?_ (fun c => ?_) c
      · simp only [Fin.snoc_last, Fin.val_last]
      · simp only [Fin.snoc_castSucc, Fin.val_castSucc]

end Per

theorem omega_pow_ne_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P) (k : Type) [Field k]
    [Algebra S.O k] [CharP k l] (ω : S.G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap S.O k (S.Γ.ε g))
    (e : ℕ) (h0 : 0 < e) (h1 : e + 1 < l) : ω ^ e ≠ 1 := by
  obtain ⟨χ, hχ, -, hs⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hz
  let a : ℕ := (z : ZMod l).val
  have ha : (a : ZMod l) = z := ZMod.natCast_zmod_val _
  have hu : IsUnit (a : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime z).symm
  have hK : S.K.1 ≤ Ks S.K 0 := le_trans (le_inf le_rfl S.hyp.1.2.1.1) le_sup_left
  obtain ⟨g, hg, hgu⟩ := hs S.K 0 hK hu.unit (by simp)
  have h2 : (S.Γ.ε ⟨g, hg⟩ : S.O) = a := by
    apply Subtype.ext
    have h3 := S.hyp.2.1.2.2.2 ⟨g, hg⟩
    rw [P.PD_χ, ← hχ, hgu] at h3
    simpa using h3
  intro h
  have h4 : ((ω ⟨g, hg⟩ : kˣ) : k) ^ e = 1 := by
    have := congrArg (fun f : S.G →* kˣ => ((f ⟨g, hg⟩ : kˣ) : k)) h
    simpa using this
  rw [hω, h2, map_natCast] at h4
  have h5 : (z : ZMod l) ^ e = 1 := by
    apply (ZMod.castHom (dvd_refl l) k).injective
    rw [← ha, map_pow, map_natCast, h4, map_one]
  have h6 : z ^ e = 1 := Units.ext (by simpa using h5)
  have := Nat.le_of_dvd h0 (orderOf_dvd_of_pow_eq_one h6)
  omega

end GlobalTheory.BasePairs
end
end

section
noncomputable section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open scoped LaurentSeries PowerSeries Pointwise

namespace GlobalTheory.BasePairs

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {k : Type} [Field k] [Algebra O k]

theorem latRep_twLat (T : LocLat G Qp LL O) (θ : G →* Oˣ) (hθ : Continuous fun g => algebraMap O LL (θ g)) (g : G)
    (x : ↥T.L.T) : latRep (twLat T θ hθ).L g x = twistRep (latRep T.L) θ g x :=
  LinearMap.congr_fun (DFunLike.congr_fun (latRep_twLattice T.L θ) g) x

theorem exists_tw_sum [IsTopologicalRing LL] {lam : O} (T T' : LocLat G Qp LL O) (θ : G →* Oˣ)
    (hθ : Continuous fun g => algebraMap O LL (θ g)) (A A' : Ob k G)
    (q : ↥(twLat T θ hθ).L.T →ₗ[O] (Fin A.m → k)) (q' : ↥(twLat T' θ hθ).L.T →ₗ[O] (Fin A'.m → k))
    (h : Onto (twLat T θ hθ) A q) (hk : KerIs lam q) (h' : Onto (twLat T' θ hθ) A' q') (hk' : KerIs lam q') :
    ∃ (C : Ob k G) (r : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T →ₗ[O] (Fin C.m → k))
      (f : LatHom (twLat T θ hθ).L (twLat (AdmClosure.prodLoc T T') θ hθ).L)
      (g : LatHom (twLat T' θ hθ).L (twLat (AdmClosure.prodLoc T T') θ hθ).L)
      (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)),
      Onto (twLat (AdmClosure.prodLoc T T') θ hθ) C r ∧ KerIs lam r ∧ Function.Bijective (a.coprod b) ∧
      Function.Bijective (f.f.coprod g.f) ∧
      (∀ z ∈ (twLat (AdmClosure.prodLoc T T') θ hθ).L.T, ∃ x ∈ (twLat T θ hθ).L.T, ∃ y ∈ (twLat T' θ hθ).L.T,
        z = f.f x + g.f y) ∧ IsHom A C a ∧ IsHom A' C b ∧
      (∀ (x : ↥(twLat T θ hθ).L.T) (x' : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T),
        (x' : (twLat (AdmClosure.prodLoc T T') θ hθ).V) = f.f x → r x' = a (q x)) ∧
      (∀ (x : ↥(twLat T' θ hθ).L.T) (x' : ↥(twLat (AdmClosure.prodLoc T T') θ hθ).L.T),
        (x' : (twLat (AdmClosure.prodLoc T T') θ hθ).V) = g.f x → r x' = b (q' x)) := by
  let Z := twLat (AdmClosure.prodLoc T T') θ hθ
  let u : ↥Z.L.T ≃ₗ[O] (↥(twLat T θ hθ).L.T × ↥(twLat T' θ hθ).L.T) := StdAdm.prodSubEquiv T.L.T T'.L.T
  obtain ⟨C, r, a, b, hr1, hr2, ha, hb, hab, hz⟩ :=
    exists_sum_reduction (twLat T θ hθ) (twLat T' θ hθ) Z u (fun _ _ => rfl) A A' q q' h hk h' hk'
  let f : LatHom (twLat T θ hθ).L Z.L :=
    { f := LinearMap.inl LL T.V T'.V
      equiv := fun g x => Prod.ext rfl (map_zero ((twLat T' θ hθ).ρ g)).symm
      cont := continuous_id.prodMk continuous_const
      T_le := fun x hx => ⟨hx, Submodule.zero_mem _⟩ }
  let g : LatHom (twLat T' θ hθ).L Z.L :=
    { f := LinearMap.inr LL T.V T'.V
      equiv := fun g x => Prod.ext (map_zero ((twLat T θ hθ).ρ g)).symm rfl
      cont := continuous_const.prodMk continuous_id
      T_le := fun x hx => ⟨Submodule.zero_mem _, hx⟩ }
  refine ⟨C, r, f, g, a, b, hr1, hr2, hab, ?_,
    fun z hz => ⟨z.1, hz.1, z.2, hz.2, Prod.ext (add_zero _).symm (zero_add _).symm⟩, ha, hb,
    fun x x' hx => ?_, fun x x' hx => ?_⟩
  · change Function.Bijective ((LinearMap.inl LL T.V T'.V).coprod (LinearMap.inr LL T.V T'.V))
    rw [LinearMap.coprod_inl_inr]
    exact Function.bijective_id
  · have h1 : (u x').1 = x := Subtype.ext (congrArg Prod.fst hx)
    have h2 : (u x').2 = 0 := Subtype.ext (congrArg Prod.snd hx)
    rw [hz, h1, h2, map_zero, map_zero, add_zero]
  · have h1 : (u x').1 = 0 := Subtype.ext (congrArg Prod.fst hx)
    have h2 : (u x').2 = x := Subtype.ext (congrArg Prod.snd hx)
    rw [hz, h1, h2, map_zero, map_zero, zero_add]

theorem sameSS_base [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (hlam : Irreducible Γ.lam)
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) {A₀ A : Ob k G}
    {q₀ : ↥(twLat Γ.T₀ Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin A₀.m → k)} (h₀ : Onto (twLat Γ.T₀ Γ.χ₁⁻¹ hθ) A₀ q₀)
    (hK₀ : KerIs Γ.lam q₀) (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g))
    {t μ : ℕ} {U : ZMod n → Multiset ℤ} {T : LocLat G Qp LL O} (hT : SumFull PD emb Γ t U μ T)
    {q : ↥(twLat T Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin A.m → k)} (h : Onto (twLat T Γ.χ₁⁻¹ hθ) A q) (hK : KerIs Γ.lam q) :
    SameSS A.ρ (piRep fun _ : Fin μ => refSum A₀ ω t) := by
  obtain ⟨e₀, he₀⟩ := exists_ref_equiv Γ hs hk A₀ q₀ h₀.1 hK₀
    (fun g x => (congrArg q₀ (latRep_twLat Γ.T₀ _ hθ g x).symm).trans (h₀.2 g x)) ω hω t
  obtain ⟨e, he⟩ := exists_quot_equiv (M := ↥T.L.T) q h.1 hK
  refine sameSS_twist_residue (π := modRep (latRep T.L) Γ.lam) (π' := piRep fun _ : Fin μ => Γ.refRep t)
    hs Γ.χ₁⁻¹ e (fun g x => ?_) (LinearEquiv.piCongrRight fun _ => e₀)
    (fun g x => funext fun j => he₀ g (x j)) (sumFull_sameSS hlam hT)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (he (twistRep (latRep T.L) Γ.χ₁⁻¹ g x)).trans
    (((congrArg q (latRep_twLat T _ hθ g x).symm).trans (h.2 g x)).trans (congrArg (A.ρ g) (he x).symm))

theorem exists_quot_of_admissible (hs : Function.Surjective (algebraMap O k)) (h0 : algebraMap O k Γ.lam = 0)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) {t : ℕ} {U : ZMod n → Multiset ℤ}
    (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
    (e : N ≃ₗ[O] (Fin A.m → k)) (hπ : Admissible PD emb Γ t U π)
    (he : ∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) :
    ∃ (μ : ℕ) (T : LocLat G Qp LL O), SumFull PD emb Γ t U μ T ∧
      ∀ (C : Ob k G) (q : ↥(twLat T Γ.χ₁⁻¹ hθ).L.T →ₗ[O] (Fin C.m → k)), Onto (twLat T Γ.χ₁⁻¹ hθ) C q →
        KerIs Γ.lam q → ∃ a, IsHom C A a ∧ Function.Surjective a := by
  obtain ⟨-, μ, T, hT, L₂, s, -, hs', hg, -⟩ := hπ
  refine ⟨μ, T, hT, fun C q hq hK => ?_⟩
  obtain ⟨a, ha⟩ := exists_descend (M := ↥T.L.T) hs h0 q hq.1 hK (e.toLinearMap ∘ₗ s)
  refine ⟨a, fun g y => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := hq.1 y
    have h1 : C.ρ g (q x) = q (twistRep (latRep T.L) Γ.χ₁⁻¹ g x) :=
      (hq.2 g x).symm.trans (congrArg q (latRep_twLat T _ hθ g x))
    have h2 : s (twistRep (latRep T.L) Γ.χ₁⁻¹ g x) = twistRep π Γ.χ₁⁻¹ g (s x) :=
      (map_smul s _ _).trans (congrArg (((Γ.χ₁⁻¹ g : Oˣ) : O) • ·) (hg g x))
    exact (congrArg a h1).trans ((ha _).trans ((congrArg e h2).trans ((he g _).trans
      (congrArg (A.ρ g) (ha x).symm))))
  · obtain ⟨x, hx⟩ := (e.surjective.comp hs') y
    exact ⟨q x, (ha x).trans hx⟩

theorem exists_chi_reduction [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hθ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (c : ℕ)
    (hc : Continuous fun g => algebraMap O LL (Γ.chi (c + 1) g))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    ∃ q, Onto (twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) Γ.χ₁⁻¹ hθ) (chr (ω ^ (-(c : ℤ)))) q ∧ KerIs Γ.lam q := by
  obtain ⟨u, -, hu⟩ := charLattice_equiv hinj (Γ.chi (c + 1))
  have hω' : ω = (Units.map (algebraMap O k : O →* k)).comp Γ.ε := MonoidHom.ext fun g => Units.ext (hω g)
  refine exists_char_reduction hs hk (twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) Γ.χ₁⁻¹ hθ) u
    (Γ.χ₁⁻¹ * Γ.chi (c + 1)) (fun g a => ?_) _ fun g => ?_
  · refine (latRep_twLat (charLat Qp hinj (Γ.chi (c + 1)) hc) _ hθ g (u a)).trans ?_
    refine (congrArg (((Γ.χ₁⁻¹ g : Oˣ) : O) • ·) (hu g a).symm).trans ?_
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • u (((Γ.chi (c + 1) g : Oˣ) : O) • a) =
      (((Γ.χ₁⁻¹ g * Γ.chi (c + 1) g : Oˣ) : O)) • u a
    rw [map_smul, smul_smul, Units.val_mul]
  · rw [hω']
    simp [GalData.chi]

theorem exists_eps_reduction [IsTopologicalRing LL] (hinj : Function.Injective (algebraMap O LL))
    (hs : Function.Surjective (algebraMap O k)) (hk : ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x)
    (hc : Continuous fun g => algebraMap O LL (Γ.ε g))
    (ω : G →* kˣ) (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    ∃ q, Onto (charLat Qp hinj Γ.ε hc) (chr (ω ^ (-(-1 : ℤ)))) q ∧ KerIs Γ.lam q := by
  obtain ⟨u, -, hu⟩ := charLattice_equiv hinj Γ.ε
  refine exists_char_reduction hs hk (charLat Qp hinj Γ.ε hc) u Γ.ε (fun g a => ?_) _ fun g => ?_
  · exact (hu g a).symm.trans (map_smul u _ _)
  · rw [neg_neg, zpow_one, hω]

end Gen

section Sit

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {k : Type} [Field k] [Algebra O k] {l : ℕ} {R : RingPG k l} {F : DFun R n G}
    {r₀ : ℕ} {D : TopData n r₀}
    {RN : ∀ (T : LocLat G Qp LL O) (A : Ob k G), (↥T.L.T →ₗ[O] (Fin A.m → k)) → Lats k n A.m → Prop}

variable (Γ RN) in

def Red (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (N : Lats k n A.m) : Prop :=
  Onto T A q ∧ KerIs Γ.lam q ∧ RN T A q N

abbrev tw (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i) (T : LocLat G Qp LL O) : LocLat G Qp LL O :=
  twLat T Γ.χ₁⁻¹ hθ.1

theorem crys_tw (htw : StdAdm.TwistRule PD emb O) (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i)
    {T : LocLat G Qp LL O} {U : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U) :
    CrysWith PD emb (tw hθ T).ρ (fun i => (U i).map (· + -D.w i)) :=
  (htw T U _ _ h hθ).1

variable (RN) in

def Base (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i) (A : Ob k G) (N : Lats k n A.m) : Prop :=
  ∃ (μ : ℕ) (T : LocLat G Qp LL O) (q : ↥(tw hθ T).L.T →ₗ[O] (Fin A.m → k)),
    SumFull PD emb Γ D.t D.Ut μ T ∧ Red Γ RN (tw hθ T) A q N

variable [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL]
  (hθ : IsCrysChar PD emb Γ.χ₁⁻¹ fun i => -D.w i)
  (hk : Function.Surjective (algebraMap O k) ∧ ∀ x, algebraMap O k x = 0 ↔ Γ.lam ∣ x) (hlam : Irreducible Γ.lam)
  (hsum : StdAdm.SumRule PD emb O) (htw : StdAdm.TwistRule PD emb O)
  (hobj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → F.Obj A)
  (hex : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∃ N : Lats k n A.m, RN T A q N ∧ ∀ i, IsLat (N i))
  (habc : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ w w' : ZMod n → ℕ, (∀ i, ∀ u ∈ U i, -(w i : ℤ) ≤ u ∧ u ≤ w' i) →
    ABC (F.D A) (fun i => w i) (fun i => w' i) N)
  (hsen : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ i x, sen ((F.D A).γ i) (N i) x = resCount (U i) 0 x)
  (hpoly : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ (i : ZMod n) (s : ℕ),
    (∀ u ∈ U i, ∀ a : ℕ, a < s → (l : ℤ) ∣ (a : ℤ) - u → (a : ℤ) = u) → EPoly ((F.D A).γ i) (N i) s)
  (hrk : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ N : Lats k n A.m, RN T A q N → ∀ a : ZMod n → ℤ, A.m = 1 → (∀ i, U i = {a i}) →
    ∀ i, pull ((F.D A).φ i) (N (i - 1)) = sh (a i) (N i))
  (hadd : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q (U : ZMod n → Multiset ℤ), Onto T A q → KerIs Γ.lam q → CrysWith PD emb T.ρ U →
    ∀ (T' : LocLat G Qp LL O) (A' : Ob k G) q' (U' : ZMod n → Multiset ℤ),
    Onto T' A' q' → KerIs Γ.lam q' → CrysWith PD emb T'.ρ U' →
    ∀ (Z : LocLat G Qp LL O) (C : Ob k G) r (V : ZMod n → Multiset ℤ),
    Onto Z C r → KerIs Γ.lam r → CrysWith PD emb Z.ρ V →
    ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) →
    (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b →
    (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) →
    (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) →
    ∀ (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m), RN T A q N → RN T' A' q' N' → RN Z C r L →
    ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i)

set_option linter.unusedSectionVars false

include hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd

theorem exists_red {T : LocLat G Qp LL O} {U : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U) :
    ∃ (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (N : Lats k n A.m),
      A.m = Module.finrank LL T.V ∧ Red Γ RN T A q N := by
  have := StdAdm.finite_lat T
  have := T.L.free
  obtain ⟨A, q, hm, hq, hK, hg⟩ := exists_reduction hk.1 hk.2 (latRep T.L)
  obtain ⟨N, hN, -⟩ := hex T A q U ⟨hq, hg⟩ hK h
  refine ⟨A, q, N, hm.trans ?_, ⟨hq, hg⟩, hK, hN⟩
  have : Submodule.IsLattice LL T.L.T := ⟨T.L.fg, T.L.span⟩
  rw [Module.finrank, Module.finrank, Submodule.IsLattice.rank' LL]

theorem exists_red_sum {T T' : LocLat G Qp LL O} {U U' : ZMod n → Multiset ℤ} (h : CrysWith PD emb T.ρ U)
    (h' : CrysWith PD emb T'.ρ U') {A A' : Ob k G} {q q' N N'} (hr : Red Γ RN (tw hθ T) A q N)
    (hr' : Red Γ RN (tw hθ T') A' q' N') :
    ∃ C r a b, IsHom A C a ∧ IsHom A' C b ∧ Function.Bijective (a.coprod b) ∧
      Red Γ RN (tw hθ (AdmClosure.prodLoc T T')) C r (fun i => F.push A C a N i ⊔ F.push A' C b N' i) := by
  obtain ⟨C, r, f, g, a, b, hr1, hr2, hab, h1, h2, ha, hb, h3, h4⟩ :=
    exists_tw_sum T T' _ hθ.1 A A' q q' hr.1 hr.2.1 hr'.1 hr'.2.1
  have hZ := crys_tw htw hθ (T := AdmClosure.prodLoc T T')
    (hsum T T' (AdmClosure.prodLoc T T') _ _ (LinearEquiv.refl _ _) (fun _ _ => rfl) h h')
  obtain ⟨L, hL, -⟩ := hex (tw hθ (AdmClosure.prodLoc T T')) C r _ hr1 hr2 hZ
  have key := hadd (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ h) (tw hθ T') A' q' _ hr'.1 hr'.2.1 (crys_tw htw hθ h') (tw hθ (AdmClosure.prodLoc T T')) C r _ hr1 hr2
    hZ f g a b h1 h2 ha hb h3 h4 N N' L hr.2.2 hr'.2.2 hL
  obtain rfl : L = fun i => F.push A C a N i ⊔ F.push A' C b N' i := funext key
  exact ⟨C, r, a, b, ha, hb, hab, hr1, hr2, hL⟩

theorem base_abc {A : Ob k G} {N} (h : Base RN hθ A N) : ABC (F.D A) D.w D.wst N := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  have key := habc (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 (fun i => (D.w i).toNat) (fun i => (D.wst i).toNat)
    (fun i u hu => by
      obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.1 hu
      have := D.mem_Ut i (Multiset.mem_of_mem_nsmul hu')
      have := w_range D i
      simp only [TopData.wst]
      omega)
  have e1 : (fun i => (((D.w i).toNat : ℕ) : ℤ)) = D.w := funext fun i => by
    have := w_range D i
    omega
  have e2 : (fun i => (((D.wst i).toNat : ℕ) : ℤ)) = D.wst := funext fun i => by
    have := w_range D i
    simp only [TopData.wst]
    omega
  rwa [e1, e2] at key

theorem base_sen {A₀ : Ob k G} {q₀ N₀} (h₀ : Red Γ RN (tw hθ Γ.T₀) A₀ q₀ N₀) (ω : G →* kˣ)
    (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) {A : Ob k G} {N} (h : Base RN hθ A N) :
    ∃ μ : ℕ, SameSS A.ρ (piRep fun _ : Fin μ => refSum A₀ ω D.t) ∧
      ∀ i x, sen ((F.D A).γ i) (N i) x = μ * resCount (D.Ut i) (D.w i) x := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  refine ⟨μ, ?_, fun i x => ?_⟩
  · exact sameSS_base hlam hk.1 hk.2 hθ.1 h₀.1 h₀.2.1 ω hω hT hr.1 hr.2.1
  · rw [hsen (tw hθ T) A q _ hr.1 hr.2.1
      (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 i x, resCount_nsmul_map]

theorem base_sum {A A' : Ob k G} {N N'} (h : Base RN hθ A N) (h' : Base RN hθ A' N') :
    ∃ C i j, IsHom A C i ∧ IsHom A' C j ∧ Function.Bijective (i.coprod j) ∧
      Base RN hθ C (fun a => F.push A C i N a ⊔ F.push A' C j N' a) := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  obtain ⟨μ', T', q', hT', hr'⟩ := h'
  obtain ⟨C, r, a, b, ha, hb, hab, hr⟩ :=
    exists_red_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (sumFull_crys hsum hT) (sumFull_crys hsum hT') hr hr'
  exact ⟨C, a, b, ha, hb, hab, μ + μ', _, r, AdmClosure.sumFull_prod hT hT', hr⟩

theorem base_e (hT1 : D.T1 l) (hT3 : D.T3 l) {A : Ob k G} {N} (h : Base RN hθ A N) (i : ZMod n) (hi : D.ty i = LType.Bd) :
    EPoly ((F.D A).γ i) (N i) (D.wst i + 1) := by
  obtain ⟨μ, T, q, hT, hr⟩ := h
  have hw := w_range D i
  have key := hpoly (tw hθ T) A q _ hr.1 hr.2.1
    (crys_tw htw hθ (sumFull_crys hsum hT)) N hr.2.2 i (D.wst i + 1).toNat
    (fun u hu a ha hd => by
      obtain ⟨u', hu', rfl⟩ := Multiset.mem_map.1 hu
      exact eq_of_dvd D hT1 hT3 i hi u' (Multiset.mem_of_mem_nsmul hu') a (by omega) hd)
  have e : (((D.wst i + 1).toNat : ℕ) : ℤ) = D.wst i + 1 := by
    simp only [TopData.wst]
    omega
  rwa [e] at key

theorem char_props {T : LocLat G Qp LL O} {e : ℤ} (h : CrysWith PD emb T.ρ fun _ => {e}) {ψ : G →* kˣ} {q N}
    (hr : Red Γ RN T (chr ψ) q N) (i : ZMod n) : IsLat (N i) ∧ CondC ((F.D (chr ψ)).γ i) (N i) ∧
      pull ((F.D (chr ψ)).φ i) (N (i - 1)) = sh e (N i) ∧
      ∀ x, sen ((F.D (chr ψ)).γ i) (N i) x = resCount {e} 0 x := by
  have key := habc T _ q _ hr.1 hr.2.1 h N hr.2.2
    (fun _ => (-e).toNat) (fun _ => e.toNat) (fun i u hu => by
      rw [Multiset.mem_singleton.1 hu]
      omega)
  exact ⟨key.1 i, key.2.2 i,
    hrk T _ q _ hr.1 hr.2.1 h N hr.2.2 (fun _ => e) rfl (fun _ => rfl) i,
    hsen T _ q _ hr.1 hr.2.1 h N hr.2.2 i⟩

theorem exists_model (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
    (e : N ≃ₗ[O] (Fin A.m → k)) (hπ : Admissible PD emb Γ D.t D.Ut π) (he : ∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) :
    ∃ L, IsModel F (Base RN hθ) A L := by
  obtain ⟨μ, T, hT, h⟩ := exists_quot_of_admissible hk.1 ((hk.2 _).2 dvd_rfl) hθ.1 A N π e hπ he
  obtain ⟨C, q, Nb, -, hr⟩ := exists_red hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (crys_tw htw hθ (sumFull_crys hsum hT))
  obtain ⟨a, ha, hs⟩ := h C q hr.1 hr.2.1
  exact ⟨_, C, Nb, C, LinearMap.id, a, ⟨μ, T, q, hT, hr⟩, fun _ _ => rfl, Function.injective_id, ha, hs, rfl⟩

theorem exists_std (hD : IsTopGal PD emb D Γ) (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    {A₀ : Ob k G} {q₀ N₀} (h₀ : Red Γ RN (tw hθ Γ.T₀) A₀ q₀ N₀) (ω : G →* kˣ)
    (hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) :
    IsModel F (Base RN hθ) A₀ N₀ ∧ ∀ e : ℤ, ∃ N : Lats k n 1,
      (-1 ≤ e → F.Obj (chr (ω ^ (-e))) ∧ ∀ i, IsLat (N i) ∧ CondC ((F.D (chr (ω ^ (-e)))).γ i) (N i) ∧
        pull ((F.D (chr (ω ^ (-e)))).φ i) (N (i - 1)) = sh e (N i) ∧
        ∀ x, sen ((F.D (chr (ω ^ (-e)))).γ i) (N i) x = resCount {e} 0 x) ∧
      (0 ≤ e → e < D.t → IsModel F (Base RN hθ) (chr (ω ^ (-e))) N) := by
  have hinj := IsFractionRing.injective O LL
  have hχ := StdAdm.isCrysChar_chi hinj htw hD.2.2.1 hε
  let X : ℕ → LocLat G Qp LL O := fun c => charLat Qp hinj _ (hχ c).1
  have hX₀ : ∀ c : ℕ, CrysWith PD emb (X c).ρ fun i => {D.w i + c} := fun c => (hχ c).2
  have hX : ∀ c : ℕ, CrysWith PD emb (tw hθ (X c)).ρ fun _ => {(c : ℤ)} := fun c => by
    have h := crys_tw htw hθ (T := X c) (hX₀ c)
    simpa using h
  have hXr : ∀ c : ℕ, ∃ q N, Red Γ RN (tw hθ (X c)) (chr (ω ^ (-(c : ℤ)))) q N := fun c => by
    obtain ⟨q, hq, hK⟩ := exists_chi_reduction (Qp := Qp) hinj hk.1 hk.2 hθ.1 c (hχ c).1 ω hω
    obtain ⟨N, hN, -⟩ := hex (tw hθ (X c)) (chr (ω ^ (-(c : ℤ)))) q _ hq hK (hX c)
    exact ⟨q, N, hq, hK, hN⟩
  choose q N hr using hXr
  obtain ⟨T, e, hT, ⟨C, r, L, hL, t0, t1⟩, he⟩ := exists_sum_ind hinj hsum hD.2.1 hχ
    (fun j T => ∃ C r L, Red Γ RN (tw hθ T) C r L ∧ IsTrace F A₀ N₀ C L ∧
      ∀ c : ℕ, c < j → IsTrace F (chr (ω ^ (-(c : ℤ)))) (N c) C L)
    ⟨A₀, q₀, N₀, h₀, IsTrace.refl F A₀ (hobj _ _ _ h₀.1) N₀, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    (fun j T hT ⟨C, r, L, hL, t0, t1⟩ => by
      obtain ⟨C', r', a, b, ha, hb, hab, hL'⟩ :=
        exists_red_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (T := T) (T' := X j) hT (hX₀ j) hL (hr j)
      have hC' := hobj _ _ _ hL'.1
      obtain ⟨s0, s1⟩ := isTrace_sum F _ _ C' a b hC' ha hb hab L (N j)
      refine ⟨C', r', _, hL', t0.trans hC' s0, fun c hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
      · exact (t1 c hc).trans hC' s0
      · exact s1) D.t
  have hB : Base RN hθ C L := ⟨1, T, r, (StdAdm.full_of_equiv hlam T e hT he).sumFull, hL⟩
  have hC' := hobj _ _ _ hL.1
  refine ⟨t0.isModel hC' hB, fun e => ?_⟩
  rcases le_or_gt 0 e with he | he
  · obtain ⟨c, rfl⟩ := Int.eq_ofNat_of_zero_le he
    exact ⟨N c, fun _ => ⟨hobj _ _ _ (hr c).1, char_props hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (hX c) (hr c)⟩,
      fun _ hc => (t1 c (by exact_mod_cast hc)).isModel hC' hB⟩
  · obtain ⟨q', hq, hK⟩ := exists_eps_reduction (Qp := Qp) hinj hk.1 hk.2 hε.1 ω hω
    let Y : LocLat G Qp LL O := charLat Qp hinj _ hε.1
    have hY : CrysWith PD emb Y.ρ fun _ => {-1} := hε.2
    obtain ⟨N', hN, -⟩ := hex Y (chr (ω ^ (-(-1 : ℤ)))) q' _ hq hK hY
    refine ⟨N', fun h => ?_, fun h => absurd h (not_le.2 he)⟩
    obtain rfl : e = -1 := by omega
    exact ⟨hobj Y _ _ hq, char_props hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (T := Y) hY ⟨hq, hK, hN⟩⟩

theorem exists_modTh [Fact l.Prime] [CharP k l] [NeZero n] (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    (hne : ∀ ω : G →* kˣ, (∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) → ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1) :
    ∃ M : ModTh F D, (∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ)) ∧
    (∃ q : ↥(tw hθ Γ.T₀).L.T →ₗ[O] (Fin M.T.m → k), Onto (tw hθ Γ.T₀ : LocLat G Qp LL O) M.T q ∧ KerIs Γ.lam q) ∧
    M.Base = Base RN hθ := by
  obtain ⟨A₀, q₀, N₀, hm, h₀⟩ := exists_red hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd (crys_tw htw hθ hD.2.1)
  let ω : G →* kˣ := (Units.map (algebraMap O k : O →* k)).comp Γ.ε
  have hω : ∀ g, (ω g : k) = algebraMap O k (Γ.ε g) := fun _ => rfl
  obtain ⟨hs, hN⟩ := exists_std hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd hD hε h₀ ω hω
  choose N hN hM using hN
  refine ⟨{ T := A₀
            T_m := hm.trans hD.1
            ω := ω
            ω_ne := hne ω hω
            Base := Base RN hθ
            base_obj := fun A N ⟨_, _, _, _, h⟩ => hobj _ _ _ h.1
            base_abc := fun A N h => base_abc hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h
            base_sen := fun A N h => base_sen hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h₀ ω hω h
            base_sum := fun A N A' N' h h' => base_sum hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h h'
            base_e := fun h1 h3 A N h => base_e hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd h1 h3 h
            Nstd := N₀
            std_model := hs
            std_sen := fun i x => ?_
            Nχ := N
            χ_obj := fun e h _ => (hN e h).1
            χ_lat := fun e h _ => (hN e h).2
            χ_model := hM
            χ_zero := eq_span_unit F (ω ^ (-(0 : ℤ))) (by simp) (N 0) (fun i => ((hN 0 (by simp)).2 i).1)
              fun i => ((hN 0 (by simp)).2 i).2.2.1 }, hω, ⟨q₀, h₀.1, h₀.2.1⟩, rfl⟩
  have h := resCount_nsmul_map 1 (D.U i) (D.w i) x
  rw [one_nsmul, one_mul] at h
  rw [hsen (tw hθ Γ.T₀) A₀ q₀ _ h₀.1 h₀.2.1
    (crys_tw htw hθ hD.2.1) N₀ h₀.2.2 i x, h]

theorem exists_real [Fact l.Prime] [CharP k l] [NeZero n] (hD : IsTopGal PD emb D Γ)
    (hε : IsCrysChar PD emb Γ.ε fun _ => -1)
    (hne : ∀ ω : G →* kˣ, (∀ g, (ω g : k) = algebraMap O k (Γ.ε g)) → ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1) :
    ∃ M : ModTh F D, (∀ σ, (M.ω σ : k) = algebraMap O k (Γ.ε σ)) ∧
      (∃ q : ↥Γ.T₀.L.T →ₗ[O] (Fin M.T.m → k), Function.Surjective q ∧
        KerIs Γ.lam q ∧ ∀ σ x, q (twistRep Γ.W₀ Γ.χ₁⁻¹ σ x) = M.T.ρ σ (q x)) ∧
      ∀ (A : Ob k G) (N : Type) [AddCommGroup N] [Module O N] (π : Representation O G N)
        (e : N ≃ₗ[O] (Fin A.m → k)), Admissible PD emb Γ D.t D.Ut π →
        (∀ σ x, e (twistRep π Γ.χ₁⁻¹ σ x) = A.ρ σ (e x)) → ∃ L, M.Model A L := by
  obtain ⟨M, h1, ⟨q, hq, hK⟩, h3⟩ := exists_modTh hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd hD hε hne
  refine ⟨M, h1, ⟨q, hq.1, hK, fun g x => (congrArg q (latRep_twLat Γ.T₀ _ hθ.1 g x).symm).trans (hq.2 g x)⟩,
    fun A N _ _ π e hπ he => ?_⟩
  have h := exists_model hθ hk hlam hsum htw hobj hex habc hsen hpoly hrk hadd A N π e hπ he
  rwa [← h3] at h

end Sit

end GlobalTheory.BasePairs
end
end
