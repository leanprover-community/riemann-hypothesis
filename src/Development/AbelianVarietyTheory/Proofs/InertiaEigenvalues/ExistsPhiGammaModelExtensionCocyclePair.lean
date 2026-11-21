import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequence
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResidues
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HomToCharacterLineEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityShiftLatticeVariablePow

section
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.JHMatch

section Mod
variable {R : Type} [Ring R]

def HasFactors (M : Type) [AddCommGroup M] [Module R M] {ι : Type} (F : ι → ModuleCat.{0} R) : Prop :=
  ∃ r : CompositionSeries (Submodule R M), r.head = ⊥ ∧ r.last = ⊤ ∧
    ∃ e : ι ≃ Fin r.length, ∀ i, Nonempty (F i ≃ₗ[R] factor r (e i))

variable {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {ι κ : Type}

theorem HasFactors.finiteLength {F : ι → ModuleCat.{0} R} (h : HasFactors M F) : IsFiniteLength R M := by
  obtain ⟨r, h1, h2, -⟩ := h
  exact isFiniteLength_of_exists_compositionSeries ⟨r, h1, h2⟩

theorem HasFactors.of_same {F : ι → ModuleCat.{0} R} (h : HasFactors M F) (h' : SameFactors R M N) :
    HasFactors N F := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  obtain ⟨s, t, h3, h4, h5, h6, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder r s (h1.trans h3.symm) (h2.trans h4.symm)
  refine ⟨t, h5, h6, (e.trans c).trans e', fun i => ?_⟩
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' (c (e i))
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g⟩

theorem HasFactors.of_equiv {F : ι → ModuleCat.{0} R} (h : HasFactors M F) (e : M ≃ₗ[R] N) :
    HasFactors N F := h.of_same (SameFactors.of_equiv h.finiteLength e)

theorem HasFactors.unique {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (h' : HasFactors M F') : ∃ e : ι ≃ κ, ∀ i, Nonempty (F i ≃ₗ[R] F' (e i)) := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  obtain ⟨s, h3, h4, e', he'⟩ := h'
  obtain ⟨c, hc⟩ := CompositionSeries.jordan_holder r s (h1.trans h3.symm) (h2.trans h4.symm)
  refine ⟨(e.trans c).trans e'.symm, fun i => ?_⟩
  obtain ⟨j, hj⟩ := e'.surjective (c (e i))
  have hj' : ((e.trans c).trans e'.symm) i = j := by
    simp [← hj]
  rw [hj']
  obtain ⟨f⟩ := he i
  obtain ⟨g⟩ := he' j
  rw [hj] at g
  exact ⟨(f.trans (JordanHolderLattice.Iso.linearEquiv (hc (e i)))).trans g.symm⟩

theorem HasFactors.reindex {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (c : ι ≃ κ) (hc : ∀ i, F' (c i) = F i) : HasFactors M F' := by
  obtain ⟨r, h1, h2, e, he⟩ := h
  refine ⟨r, h1, h2, c.symm.trans e, fun j => ?_⟩
  obtain ⟨i, rfl⟩ := c.surjective j
  rw [hc, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact he i

theorem HasFactors.simple [IsSimpleModule R M] : HasFactors M (fun _ : Unit => ModuleCat.of R M) := by
  let r : CompositionSeries (Submodule R M) :=
    { length := 1
      toFun := ![⊥, ⊤]
      step := fun i => by
        fin_cases i
        exact bot_covBy_top }
  refine ⟨r, rfl, rfl, Equiv.ofUnique Unit (Fin 1), fun i => ⟨?_⟩⟩
  change M ≃ₗ[R] (↥(⊤ : Submodule R M) ⧸ (⊥ : Submodule R M).comap (⊤ : Submodule R M).subtype)
  exact Submodule.topEquiv.symm.trans (Submodule.quotEquivOfEqBot _ (by simp)).symm

theorem HasFactors.prod {F : ι → ModuleCat.{0} R} {F' : κ → ModuleCat.{0} R} (h : HasFactors M F)
    (h' : HasFactors N F') : HasFactors (M × N) (Sum.elim F F') := by
  obtain ⟨t, h1, h2, a, ha⟩ := h
  obtain ⟨s, h3, h4, c, hc⟩ := h'
  obtain ⟨r, h5, h6, e, he1, he2⟩ := exists_series_of_exact (R := R) (A := M) (C := N)
    LinearMap.inl_injective LinearMap.snd_surjective .inl_snd t h1 h2 s h3 h4
  refine ⟨r, h5, h6, (a.sumCongr c).trans e, ?_⟩
  rintro (i | j)
  · obtain ⟨u⟩ := ha i
    obtain ⟨v⟩ := he1 (a i)
    exact ⟨u.trans v⟩
  · obtain ⟨u⟩ := hc j
    obtain ⟨v⟩ := he2 (c j)
    exact ⟨u.trans v⟩

theorem HasFactors.zero [Subsingleton M] [IsEmpty ι] (F : ι → ModuleCat.{0} R) : HasFactors M F := by
  refine ⟨RelSeries.singleton _ ⊥, rfl, Subsingleton.elim _ _, Equiv.equivOfIsEmpty ι (Fin 0), fun i => ?_⟩
  exact isEmptyElim i

def succEquiv (m : ℕ) (ι : Type) : ι ⊕ (Fin m × ι) ≃ Fin (m + 1) × ι where
  toFun := Sum.elim (fun i => (0, i)) (fun p => (p.1.succ, p.2))
  invFun := fun p => Fin.cases (motive := fun _ => ι ⊕ (Fin m × ι)) (Sum.inl p.2) (fun j => Sum.inr (j, p.2)) p.1
  left_inv := by rintro (i | ⟨j, i⟩) <;> simp
  right_inv := by
    rintro ⟨j, i⟩
    induction j using Fin.cases <;> simp

theorem HasFactors.pi : ∀ {m : ℕ} {N : Fin m → Type} [∀ j, AddCommGroup (N j)] [∀ j, Module R (N j)]
    {F : Fin m → ι → ModuleCat.{0} R}, (∀ j, HasFactors (N j) (F j)) →
    HasFactors (∀ j, N j) (fun p : Fin m × ι => F p.1 p.2)
  | 0, _, _, _, _, _ => HasFactors.zero _
  | m + 1, N, _, _, F, h =>
    (((h 0).prod (HasFactors.pi (F := fun j => F j.succ) fun j => h (Fin.succ j))).of_equiv
      (Fin.consLinearEquiv R N)).reindex (succEquiv m ι) (by rintro (i | ⟨j, i⟩) <;> rfl)

end Mod

section Rep
variable {k G : Type} [Field k] [Group G]

theorem equivariant_of_linear {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    {π : Representation k G M} {π' : Representation k G N}
    (f : π.asModule →ₗ[MonoidAlgebra k G] π'.asModule) :
    ∃ f' : M →ₗ[k] N, (∀ g x, f' (π g x) = π' g (f' x)) ∧
      ∀ x, f' (π.asModuleEquiv x) = π'.asModuleEquiv (f x) := by
  let u := (Representation.IntertwiningMap.equivLinearMapAsModule π π').symm f
  exact ⟨u.toLinearMap, fun g x => LinearMap.congr_fun (u.isIntertwining' g) x, fun _ => rfl⟩

theorem chr_simple (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  have h : IsSimpleModule k (chr χ).ρ.asModule := by
    rw [isSimpleModule_iff_finrank_eq_one, (chr χ).ρ.asModuleEquiv.finrank_eq]
    simp
  have := IsSimpleModule.nontrivial k (chr χ).ρ.asModule
  refine { eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_bot_or_eq_top (S.restrictScalars k) with h | h
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

def prodAsModule {M N : Type} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    (π : Representation k G M) (π' : Representation k G N) :
    (π.prod π').asModule ≃ₗ[MonoidAlgebra k G] π.asModule × π'.asModule :=
  LinearEquiv.ofBijective
    (LinearMap.prod (asModuleMap (π := π.prod π') (π' := π) (LinearMap.fst k M N) fun _ _ => rfl)
      (asModuleMap (π := π.prod π') (π' := π') (LinearMap.snd k M N) fun _ _ => rfl))
    (Function.bijective_id (α := M × N))

theorem exists_subquot (T C : Ob k G) (Y : Submodule (MonoidAlgebra k G) T.ρ.asModule)
    (q : Y →ₗ[MonoidAlgebra k G] C.ρ.asModule) (hq : Function.Surjective q) :
    ∃ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A₁ T j ∧ Function.Injective j ∧ IsHom A₁ C p ∧ Function.Surjective p := by
  have : Module.Finite k T.ρ.asModule := Module.Finite.equiv T.ρ.asModuleEquiv.symm
  have : Module.Finite k Y :=
    Module.Finite.of_injective (Y.subtype.restrictScalars k) Y.subtype_injective
  obtain ⟨A, e, he⟩ := exists_ob (Representation.ofModule' (k := k) (G := G) Y)
  have key : ∀ g x, e.symm (A.ρ g x) = MonoidAlgebra.of k G g • e.symm x := fun g x => by
    apply e.injective
    rw [e.apply_symm_apply]
    have := he g (e.symm x)
    rw [e.apply_symm_apply] at this
    rw [← this]
    congr 1
  refine ⟨A, T.ρ.asModuleEquiv.toLinearMap ∘ₗ Y.subtype.restrictScalars k ∘ₗ e.symm.toLinearMap,
    C.ρ.asModuleEquiv.toLinearMap ∘ₗ q.restrictScalars k ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    T.ρ.asModuleEquiv.injective.comp (Y.subtype_injective.comp e.symm.injective), fun g x => ?_,
    C.ρ.asModuleEquiv.surjective.comp (hq.comp e.symm.surjective)⟩
  · simp [key, Representation.asModuleEquiv_map_smul]
    rfl
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.restrictScalars_apply, key, map_smul]
    simp [Representation.asModuleEquiv_map_smul]
    rfl

theorem jh_match : ∀ {k G : Type} [Field k] [Group G] (T : Ob k G) (ω : G →* kˣ) (t μ s : ℕ) (C : Fin s → Ob k G), (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) → SameSS (piRep fun a => (C a).ρ) (piRep fun _ : Fin μ => refSum T ω t) → ∃ c : Fin s → Option (Fin t), (∀ a e, c a = some e → ∃ f, IsHom (C a) (chr (ω ^ (-(e.val : ℤ)))) f ∧ Function.Bijective f) ∧ (∀ a, c a = none → ∃ (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin (C a).m → k)), IsHom A₁ T j ∧ Function.Injective j ∧ IsHom A₁ (C a) p ∧ Function.Surjective p) ∧ ∀ e, (Finset.univ.filter fun a => c a = some e).card = μ := by
  intro k G _ _ T ω t μ s C hC h
  have hT : IsFiniteLength (MonoidAlgebra k G) T.ρ.asModule :=
    finiteLength_asModule T.ρ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  obtain ⟨r, hr1, hr2⟩ := isFiniteLength_iff_exists_compositionSeries.mp hT
  have fT : HasFactors T.ρ.asModule (fun i : Fin r.length => ModuleCat.of (MonoidAlgebra k G) (factor r i)) :=
    ⟨r, hr1, hr2, Equiv.refl _, fun _ => ⟨LinearEquiv.refl _ _⟩⟩
  have fL := (HasFactors.pi (N := fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ.asModule) fun e =>
    @HasFactors.simple _ _ _ _ _ (chr_simple (ω ^ (-(e.val : ℤ))))).of_equiv
      (piAsModule fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ).symm
  have fR := (fT.prod fL).of_equiv (prodAsModule _ _).symm
  have fS := (HasFactors.pi (N := fun _ : Fin μ => (refSum T ω t).asModule) fun _ => fR).of_equiv
    (piAsModule fun _ : Fin μ => refSum T ω t).symm
  have fC := ((HasFactors.pi (N := fun a => (C a).ρ.asModule) fun a =>
    @HasFactors.simple _ _ _ _ _ (hC a)).of_equiv (piAsModule fun a => (C a).ρ).symm).of_same h
  obtain ⟨e, he⟩ := fC.unique fS
  refine ⟨fun a => Sum.elim (fun _ => none) (fun p => some p.1) (e (a, ())).2, fun a x hx => ?_,
    fun a hx => ?_, fun x => ?_⟩
  · obtain ⟨u⟩ := he (a, ())
    beta_reduce at hx
    generalize e (a, ()) = z at hx u
    rcases z with ⟨b, i | ⟨y, w⟩⟩
    · simp at hx
    · obtain rfl : y = x := by simpa using hx
      obtain ⟨f, hf1, hf2⟩ := equivariant_of_linear (π := (C a).ρ) (π' := (chr (ω ^ (-(y.val : ℤ)))).ρ) u.toLinearMap
      refine ⟨f, hf1, ?_⟩
      have : ⇑f ∘ (C a).ρ.asModuleEquiv = (chr (ω ^ (-(y.val : ℤ)))).ρ.asModuleEquiv ∘ u := funext hf2
      rw [← Function.Bijective.of_comp_iff _ (C a).ρ.asModuleEquiv.bijective, this]
      exact (LinearEquiv.bijective _).comp u.bijective
  · obtain ⟨u⟩ := he (a, ())
    beta_reduce at hx
    generalize e (a, ()) = z at hx u
    rcases z with ⟨b, i | ⟨y, w⟩⟩
    · let u' : (C a).ρ.asModule ≃ₗ[MonoidAlgebra k G] factor r i := u
      exact exists_subquot T (C a) (r i.succ) (u'.symm.toLinearMap ∘ₗ Submodule.mkQ _)
        (u'.symm.surjective.comp (Submodule.mkQ_surjective _))
    · simp at hx
  · refine Eq.trans ?_ (Finset.card_fin μ)
    symm
    refine Finset.card_bij (fun b _ => (e.symm (b, Sum.inr (x, ()))).1) (fun b _ => ?_) (fun b _ b' _ hb => ?_)
      (fun a ha => ?_)
    · have : ((e.symm (b, Sum.inr (x, ()))).1, ()) = e.symm (b, Sum.inr (x, ())) := rfl
      simp [this]
    · have : e.symm (b, Sum.inr (x, ())) = e.symm (b', Sum.inr (x, ())) := Prod.ext hb rfl
      simpa using this
    · refine ⟨(e (a, ())).1, Finset.mem_univ _, ?_⟩
      have h2 : (e (a, ())).2 = Sum.inr (x, ()) := by
        have := (Finset.mem_filter.mp ha).2
        beta_reduce at this
        generalize (e (a, ())).2 = z at this
        rcases z with i | ⟨y, w⟩
        · simp at this
        · simpa using this
      rw [← h2]
      simp

end Rep
end GlobalTheory.JHMatch
end
end

section
section
noncomputable section
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open scoped LaurentSeries PowerSeries

theorem exists_simple_quotient {k G : Type} [Field k] [Group G] (B : Ob k G) (hB : B.m ≠ 0) :
    ∃ (A C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom A B f ∧ IsHom B C p ∧ Function.Injective f ∧ Function.Surjective p ∧ Function.Exact f p ∧
      IsSimpleModule (MonoidAlgebra k G) C.ρ.asModule ∧ A.m < B.m := by
  haveI : Nonempty (Fin B.m) := ⟨⟨0, Nat.pos_of_ne_zero hB⟩⟩
  haveI : Nontrivial B.ρ.asModule := B.ρ.asModuleEquiv.toEquiv.nontrivial
  have hfl := finiteLength_asModule B.ρ
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  obtain ⟨S, hS, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (MonoidAlgebra k G) B.ρ.asModule)).resolve_left
    bot_ne_top
  let S' : Submodule k (Fin B.m → k) := (S.restrictScalars k).comap B.ρ.asModuleEquiv.symm.toLinearMap
  have hinv : ∀ g, S' ≤ S'.comap (B.ρ g) := by
    intro g x hx
    have hx' : B.ρ.asModuleEquiv.symm x ∈ S := hx
    change B.ρ.asModuleEquiv.symm (B.ρ g x) ∈ S
    rw [Representation.asModuleEquiv_symm_map_rho]
    exact S.smul_mem _ hx'
  obtain ⟨A, eA, hA⟩ := exists_ob (B.ρ.subrepresentation S' hinv)
  obtain ⟨C, eC, hC⟩ := exists_ob (B.ρ.quotient S' hinv)
  have hp : IsHom B C (eC.toLinearMap ∘ₗ S'.mkQ) := fun g x => hC g (S'.mkQ x)
  have hps : Function.Surjective (eC.toLinearMap ∘ₗ S'.mkQ) := eC.surjective.comp S'.mkQ_surjective
  refine ⟨A, C, S'.subtype ∘ₗ eA.symm.toLinearMap, eC.toLinearMap ∘ₗ S'.mkQ, ?_, hp,
    S'.subtype_injective.comp eA.symm.injective, hps, ?_, ?_, ?_⟩
  · intro g x
    obtain ⟨y, rfl⟩ := eA.surjective x
    rw [← hA]
    simp
  · intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_range, Submodule.subtype_apply]
    exact ⟨fun h => ⟨eA ⟨x, h⟩, by simp⟩, fun ⟨y, hy⟩ => hy ▸ (eA.symm y).2⟩
  · let q := asModuleMap (π := B.ρ) (π' := C.ρ) _ hp
    have hq : Function.Surjective q := hps
    have hk : S = LinearMap.ker q := by
      ext x
      change _ ↔ eC (S'.mkQ (B.ρ.asModuleEquiv x)) = 0
      rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Iff.rfl
    haveI := isSimpleModule_iff_isCoatom.mpr hS
    exact IsSimpleModule.congr ((Submodule.quotEquivOfEq _ _ hk).trans (q.quotKerEquivOfSurjective hq)).symm
  · have h1 : S' ≠ ⊤ := by
      intro h
      refine hS.1 (eq_top_iff.mpr fun x _ => ?_)
      have : B.ρ.asModuleEquiv x ∈ S' := h ▸ Submodule.mem_top
      exact this
    have h2 := Submodule.finrank_lt h1
    rw [eA.finrank_eq] at h2
    simpa using h2

theorem sameSS_piRep_succ {k G : Type} [Field k] [Group G] {s : ℕ} (C : Fin (s + 1) → Ob k G) (A B : Ob k G)
    (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin (C 0).m → k))
    (ef : IsHom A B f) (ep : IsHom B (C 0) p) (hf : Function.Injective f) (hp : Function.Surjective p)
    (H : Function.Exact f p) (h : SameSS A.ρ (piRep fun a : Fin s => (C a.succ).ρ)) :
    SameSS B.ρ (piRep fun a => (C a).ρ) := by
  have h1 : SameSS B.ρ ((C 0).ρ.prod (piRep fun a : Fin s => (C a.succ).ρ)) :=
    SameSS.of_exact_of_exact ef ep hf hp H (f' := LinearMap.inr k _ _) (p' := LinearMap.fst k _ _)
      (fun g x => by simp) (fun g x => by simp) LinearMap.inr_injective LinearMap.fst_surjective .inr_fst h
      (SameSS.refl _ (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩))
  refine h1.congr_right (Fin.consLinearEquiv k fun a => Fin (C a).m → k) fun g x => ?_
  funext a
  refine Fin.cases ?_ (fun j => ?_) a <;> rfl

theorem ModTh.exists_simple_pieces : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  intro k G _ _ l n _ _ _ R F r Dt M B
  induction B using (measure fun A : Ob k G => A.m).wf.induction with
  | _ B ih =>
  intro N hN
  by_cases hB : B.m = 0
  · haveI : IsEmpty (Fin B.m) := ⟨fun a => by have := a.2; omega⟩
    refine ⟨0, Fin.elim0, fun a => a.elim0, fun a => a.elim0, fun a => a.elim0, ?_, fun i x => ?_⟩
    · exact SameSS.of_equiv (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
        (LinearEquiv.ofSubsingleton _ _) fun _ _ => Subsingleton.elim _ _
    · rw [Finset.univ_eq_empty, Finset.sum_empty]
      unfold sen qmult gmult
      exact Module.finrank_zero_of_subsingleton
  · obtain ⟨A, C₀, f, p, ef, ep, hf, hp, H, hs, hlt⟩ := exists_simple_quotient B hB
    obtain ⟨s, C, L, hL, hC, hss, hsen⟩ := ih A hlt _ (GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A B f N ef hf hN)
    obtain ⟨hobj, hlat, -, hc⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
    let C' : Fin (s + 1) → Ob k G := Fin.cons C₀ C
    refine ⟨s + 1, C', Fin.cons (α := fun a => Lats k n (C' a).m) (F.push B C₀ p N) L, fun a => ?_, fun a => ?_,
      sameSS_piRep_succ C' A B f p ef ep hf hp H hss, fun i x => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact ModTh.model_push_of_surjective F M B C₀ p N ep hp hN
      · exact hL j
    · refine Fin.cases ?_ (fun j => ?_) a
      · exact hs
      · exact hC j
    · rw [Fin.sum_univ_succ, GlobalTheory.T.senMultiplicity_additive_exact_sequence F A B C₀ f p N hobj ef ep hf hp H i (hlat i) (hc i) x, hsen, add_comm]
      rfl

end GlobalTheory.Models
end
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simple_pieces_sen_sum : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m), M.Model B N → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ ∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x := by
  atlas_forward_decl GlobalTheory.Models.ModTh.exists_simple_pieces
end

section
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models.ThroughLine

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (K : Ob k G) (f : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A f ∧ Function.Injective f ∧ Function.Exact f p := by
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) (fun g x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hp g x, LinearMap.mem_ker.mp hx, map_zero]))
  refine ⟨K, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (LinearMap.ker p).subtype_injective.comp e.symm.injective, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [← he]
    simp
  · exact ⟨e ⟨y, hy⟩, by simp⟩
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact j q := by
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) (fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨A.ρ g y, hj g y⟩))
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => he g (Submodule.Quotient.mk x),
    e.surjective.comp (LinearMap.range j).mkQ_surjective, fun y => ?_⟩
  simp [Submodule.Quotient.mk_eq_zero]

theorem simple_chr (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have h : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule k (Fin 1 → k)) (congrArg Subrepresentation.toSubmodule h')
  · rcases eq_bot_or_eq_top S.toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.toSubmodule_injective h')
    · exact Or.inr (Subrepresentation.toSubmodule_injective h')

theorem sameSS_three {s t u : ℕ} {M : Type} [AddCommGroup M] [Module k M] {π : Representation k G M}
    (C : (Fin s ⊕ Unit) ⊕ Fin t → Ob k G) (e : Fin u ≃ (Fin s ⊕ Unit) ⊕ Fin t)
    (h : SameSS π (((piRep fun a => (C (.inl (.inl a))).ρ).prod (C (.inl (.inr ()))).ρ).prod
      (piRep fun a => (C (.inr a)).ρ))) : SameSS π (piRep fun a => (C (e a)).ρ) := by
  have h1 : SameSS π (piRep fun a => (C a).ρ) := by
    refine h.congr_right
      ((((LinearEquiv.refl k _).prodCongr (LinearEquiv.piUnique k (fun a : Unit => Fin (C (.inl (.inr a))).m → k)).symm).trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s) Unit (fun a => Fin (C (.inl a)).m → k)).symm).prodCongr
          (LinearEquiv.refl k _) |>.trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s ⊕ Unit) (Fin t) (fun a => Fin (C a).m → k)).symm) ?_
    intro g x
    funext a
    rcases a with (a | a) | a <;> rfl
  refine h1.congr_right (LinearEquiv.piCongrLeft k (fun a => Fin (C a).m → k) e).symm ?_
  intro g x
  rfl

end GlobalTheory.Models.ThroughLine

open GlobalTheory.Models.ThroughLine in

theorem GlobalTheory.Models.ModTh.exists_jordanHolder_through_line : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  intro k G _ _ l n _ _ _ R F r Dt M B A₁ χ j p N hN hj hji hp hps
  obtain ⟨K, f, hf, hfi, hfe⟩ := exists_ker A₁ (chr χ) p hp
  obtain ⟨Q, q, hq, hqs, hqe⟩ := exists_coker A₁ B j hj
  have hA := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ B j N hj hji hN
  have hK := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M K A₁ f _ hf hfi hA
  have hL := GlobalTheory.Models.ModTh.model_push_of_surjective F M A₁ (chr χ) p _ hp hps hA
  have hQ := GlobalTheory.Models.ModTh.model_push_of_surjective F M B Q q _ hq hqs hN
  obtain ⟨s, C, L, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M K _ hK
  obtain ⟨t, C', L', d1, d2, d3, d4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M Q _ hQ
  obtain ⟨oB, lB, -, cB⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
  obtain ⟨oA, lA, -, cA⟩ := GlobalTheory.T.obj_and_abc_of_model F M A₁ _ hA
  let S : (Fin s ⊕ Unit) ⊕ Fin t → Σ A : Ob k G, Lats k n A.m :=
    Sum.elim (Sum.elim (fun a => ⟨C a, L a⟩) fun _ => ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩)
      fun a => ⟨C' a, L' a⟩
  let e := (Fintype.equivFin ((Fin s ⊕ Unit) ⊕ Fin t)).symm
  have hfl : ∀ m : ℕ, IsFiniteLength k (Fin m → k) := fun m =>
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨_, fun a => (S (e a)).1, fun a => (S (e a)).2, e.symm (.inl (.inr ())), fun a => ?_, fun a => ?_,
    ?_, fun i x => ?_, ?_⟩
  · show M.Model (S (e a)).1 (S (e a)).2
    rcases e a with (b | b) | b
    exacts [c1 b, hL, d1 b]
  · show IsSimpleModule (MonoidAlgebra k G) (S (e a)).1.ρ.asModule
    rcases e a with (b | b) | b
    exacts [c2 b, simple_chr χ, d2 b]
  · refine sameSS_three (fun a => (S a).1) e ?_
    exact (SameSS.of_exact hj hq hji hqs hqe (hfl _)).trans
      (((SameSS.of_exact hf hp hfi hps hfe (hfl _)).trans (c3.prod (SameSS.refl _ (hfl _)))).prod d3)
  · rw [Equiv.sum_comp e (fun a => sen ((F.D (S a).1).γ i) ((S a).2 i) x), Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit),
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B Q j q N oB hj hq hji hqs hqe i (lB i) (cB i) x,
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ (chr χ) f p _ oA hf hp hfi hps hfe i (lA i) (cA i) x, c4, d4]
    rfl
  · show S (e (e.symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jordanHolder_through_line_alt : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  atlas_forward_decl GlobalTheory.Models.ModTh.exists_jordanHolder_through_line
end

section
section
noncomputable section
namespace GlobalTheory.Models.CharSign
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V]

theorem exists_unit_zpow {c : k⸨X⸩} (hc : c ≠ 0) :
    ∃ (a : ℤ) (u : (k⟦X⟧)ˣ), c = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a := by
  obtain ⟨a, u, h⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (R := k⟦X⟧) (K := k⸨X⸩) PowerSeries.X_irreducible hc
  refine ⟨a, u, ?_⟩
  rw [h, Units.smul_def, Algebra.smul_def, vv_eq_coe_X]
  rfl

theorem coe_smul (a : k⟦X⟧) (x : V) : (a : k⸨X⸩) • x = a • x := algebraMap_smul k⸨X⸩ a x

theorem le_of_sh_le_sh {N : Submodule k⟦X⟧ V} (hN : N.FG) (h0 : N ≠ ⊥) {a b : ℤ} (h : sh a N ≤ sh b N) :
    b ≤ a := by
  by_contra hab
  have h1 : N ≤ sh 1 N := by
    have h2 := sh_le_sh (-a) h
    rw [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq] at h2
    exact h2.trans (sh_le_sh_of_le (by omega) N)
  apply h0
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {(PowerSeries.X : k⟦X⟧)}) N hN ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 (h1 hx)
    rw [zpow_one, vv_eq_coe_X, coe_smul]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hy
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PowerSeries.maximalIdeal_eq_span_X]

theorem span_unit_zpow (a : ℤ) (u : (k⟦X⟧)ˣ) (y : V) :
    Submodule.span k⟦X⟧ {(((u : k⟦X⟧) : k⸨X⸩) * vv k ^ a) • y} = sh a (Submodule.span k⟦X⟧ {y}) := by
  rw [sh, Submodule.map_span, Set.image_singleton, mul_smul, coe_smul,
    Submodule.span_singleton_smul_eq u.isUnit]
  rfl

theorem φ_zpow {l : ℕ} (R : RingPG k l) (a : ℤ) :
    ∃ u : (k⟦X⟧)ˣ, R.φ (vv k ^ a) = ((u : k⟦X⟧) : k⸨X⸩) * vv k ^ (l * a) := by
  obtain ⟨u, hu⟩ := R.φ_v
  refine ⟨u ^ a, ?_⟩
  rw [map_zpow₀, hu, mul_zpow, zpow_mul, zpow_natCast]
  congr 1
  have := map_zpow (Units.map (HahnSeries.ofPowerSeries ℤ k : k⟦X⟧ →+* k⸨X⸩).toMonoidHom) u a
  have h2 := congrArg Units.val this
  rw [Units.val_zpow_eq_zpow_val] at h2
  exact h2.symm

variable [Module k V]

theorem pull_sh_le {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) ≤ sh (l * a) (pull f N) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := mem_sh_iff_exists.1 hx
  obtain ⟨u, hu⟩ := φ_zpow R a
  rw [hf, hu, mul_smul, coe_smul]
  exact Submodule.smul_mem _ _ (mem_sh_iff_exists.2 ⟨f y, Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩)

theorem pull_sh {l : ℕ} (R : RingPG k l) {f : V →ₗ[k] V} (hf : Semi R.φ f) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    pull f (sh a N) = sh (l * a) (pull f N) := by
  refine le_antisymm (pull_sh_le R hf a N) ?_
  have h := sh_le_sh (l * a) (pull_sh_le R hf (-a) (sh a N))
  rwa [sh_sh_eq, sh_sh_eq, neg_add_cancel, sh_zero_eq, mul_neg, add_neg_cancel, sh_zero_eq] at h

end

section
variable {k : Type} [Field k]

theorem exists_smul_eq {y : Vc k 1} (hy : y ≠ 0) (x : Vc k 1) : ∃ c : k⸨X⸩, x = c • y := by
  have h0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
  refine ⟨x 0 / y 0, funext fun j => ?_⟩
  rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ h0]

theorem span_eq_sh {x y : Vc k 1} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ a : ℤ, Submodule.span k⟦X⟧ {x} = sh a (Submodule.span k⟦X⟧ {y}) := by
  obtain ⟨c, rfl⟩ := exists_smul_eq hy x
  obtain ⟨a, u, rfl⟩ := exists_unit_zpow (c := c) (by rintro rfl; exact hx (zero_smul _ _))
  exact ⟨a, span_unit_zpow a u y⟩

theorem span_total (x y : Vc k 1) : Submodule.span k⟦X⟧ {x} ≤ Submodule.span k⟦X⟧ {y} ∨
    Submodule.span k⟦X⟧ {y} ≤ Submodule.span k⟦X⟧ {x} := by
  by_cases hx : x = 0
  · left; simp [hx]
  by_cases hy : y = 0
  · right; simp [hy]
  obtain ⟨a, h⟩ := span_eq_sh hx hy
  rw [h]
  rcases le_total 0 a with ha | ha
  · left; exact (sh_le_sh_of_le ha _).trans (sh_zero_eq _).le
  · right; exact (sh_zero_eq _).ge.trans (sh_le_sh_of_le ha _)

theorem exists_gen {N : Submodule k⟦X⟧ (Vc k 1)} (hN : N.FG) : ∃ x, N = Submodule.span k⟦X⟧ {x} := by
  classical
  obtain ⟨s, rfl⟩ := hN
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s _ ih =>
    obtain ⟨x, hx⟩ := ih
    rw [Finset.coe_insert, Submodule.span_insert, hx]
    rcases span_total a x with h | h
    · exact ⟨x, sup_eq_right.2 h⟩
    · exact ⟨a, sup_eq_left.2 h⟩

theorem ne_bot_of_isLat {N : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) : N ≠ ⊥ := by
  rintro rfl
  have h := hN.2
  simp at h

theorem exists_eq_sh {N N' : Submodule k⟦X⟧ (Vc k 1)} (hN : IsLat N) (hN' : IsLat N') : ∃ a : ℤ, N = sh a N' := by
  obtain ⟨x, rfl⟩ := exists_gen hN.1
  obtain ⟨y, rfl⟩ := exists_gen hN'.1
  refine span_eq_sh ?_ ?_
  · rintro rfl; exact ne_bot_of_isLat hN (by simp)
  · rintro rfl; exact ne_bot_of_isLat hN' (by simp)

end

theorem model_char_sign : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → ∃ κ : ZMod n → ℤ, ∀ i, N i = sh (κ i) (M.Nχ e i) ∧ |κ i| ≤ Dt.sg l i ∧ (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧ ∀ x, sen ((F.D (chr (M.ω ^ (-e)))).γ i) (N i) x = resCount {e - κ i} 0 x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 _ _ e he0 het N hN
  obtain ⟨-, hL, hAB, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) N hN
  obtain ⟨-, hL0, hAB0, -⟩ := GlobalTheory.T.obj_and_abc_of_model F M (chr (M.ω ^ (-e))) (M.Nχ e) (M.χ_model e he0 het)
  have hχ := M.χ_lat e (by omega) het
  choose κ hκ using fun i => exists_eq_sh (hL i) (hL0 i)
  have key : ∀ i {a b : ℤ}, sh a (M.Nχ e i) ≤ sh b (M.Nχ e i) → b ≤ a :=
    fun i a b h => le_of_sh_le_sh (hL0 i).1 (ne_bot_of_isLat (hL0 i)) h
  have habs : ∀ i, |κ i| ≤ Dt.sg l i := by
    intro i
    have a1 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w N (M.Nχ e) hL hL0 hAB hAB0 i
    have a2 := GlobalTheory.PhiGam.CloseTw.main (F.D (chr (M.ω ^ (-e)))) Dt.h Dt.w (M.Nχ e) N hL0 hL hAB0 hAB i
    rw [hκ i, sh_sh_eq] at a1
    rw [hκ i] at a2
    have b1 := key i (a1.trans (sh_zero_eq _).ge)
    have b2 := key i a2
    unfold TopData.sg
    rw [abs_le]
    constructor <;> omega
  have hJ : ∀ i, -Dt.w i + κ i ≤ l * κ (i - 1) + e ∧ l * κ (i - 1) + e ≤ Dt.wst i + κ i := by
    intro i
    obtain ⟨a1, a2⟩ := hAB i
    have hp : pull ((F.D (chr (M.ω ^ (-e)))).φ i) (N (i - 1)) = sh (l * κ (i - 1) + e) (M.Nχ e i) := by
      rw [hκ (i - 1), pull_sh R ((F.D (chr (M.ω ^ (-e)))).φ_semi i), (hχ i).2.2.1, sh_sh_eq]
    rw [hp, hκ i, sh_sh_eq] at a1 a2
    exact ⟨key i a1, key i a2⟩
  refine ⟨κ, fun i => ⟨hκ i, habs i, fun hi => ?_, fun hi => ?_, fun x => ?_⟩⟩
  · by_contra hneg
    have c1 := (Dt.lowG i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).2
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).1
    have c5 : (l : ℤ) * κ (i - 1) ≤ l * (-1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · by_contra hneg
    have c1 := (Dt.lowBd i hi (Dt.w i + e) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩)))).1
    have c2 : (Dt.η i : ℤ) + 4 * Dt.sg l i + 6 < l := by exact_mod_cast h1 i
    have c3 := abs_le.1 (habs i)
    have c4 := (hJ i).2
    unfold TopData.wst at c4
    have c5 : (l : ℤ) * 1 ≤ l * κ (i - 1) := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    omega
  · rw [hκ i, GlobalTheory.PhiGam.SenShift.sen_sh R _ ((F.D (chr (M.ω ^ (-e)))).γ_semi i) _ (hχ i).1 (hχ i).2.1,
      (hχ i).2.2.2]
    unfold resCount
    have : (((e - 0 : ℤ) : k) = x + (κ i : k)) ↔ (((e - κ i - 0 : ℤ) : k) = x) := by
      push_cast
      rw [sub_zero, sub_zero, sub_eq_iff_eq_add]
    classical
    simp only [Multiset.filter_singleton, this]
    split_ifs <;> simp

end GlobalTheory.Models.CharSign
end
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_model_exponents_signs_senWeight : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → ∃ κ : ZMod n → ℤ, ∀ i, N i = sh (κ i) (M.Nχ e i) ∧ |κ i| ≤ Dt.sg l i ∧ (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧ ∀ x, sen ((F.D (chr (M.ω ^ (-e)))).γ i) (N i) x = resCount {e - κ i} 0 x := by
  atlas_forward_decl GlobalTheory.Models.CharSign.model_char_sign
end

section
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.CharModel

theorem eq_chr_of_bijective {k G : Type} [Field k] [Group G] (A : Ob k G) (χ : G →* kˣ)
    (f : (Fin A.m → k) →ₗ[k] (Fin 1 → k)) (hf : IsHom A (chr χ) f) (hb : Function.Bijective f) : A = chr χ := by
  obtain ⟨m, ρ⟩ := A
  have hm : m = 1 := by
    have := (LinearEquiv.ofBijective f hb).finrank_eq
    simpa using this
  subst hm
  have : ρ = (chr χ).ρ := by
    ext1 g
    refine LinearMap.ext fun x => hb.1 ?_
    rw [hf g x]
    change (χ g : k) • f x = f ((χ g : k) • x)
    rw [map_smul]
  subst this
  rfl

theorem chr_inj {k G : Type} [Field k] [Group G] {χ χ' : G →* kˣ} (h : chr χ = chr χ') : χ = χ' := by
  have h1 : (chr χ).ρ = (chr χ').ρ := eq_of_heq (Ob.mk.inj h).2
  ext g
  have := congrArg (fun ρ : Representation k G (Fin 1 → k) => ρ g (fun _ => 1) 0) h1
  simpa using this

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {a b : ℤ} (h : (a : k) = b) (hab : |a - b| < l) :
    a = b := by
  have h1 : ((a - b : ℤ) : k) = 0 := by push_cast; rw [h, sub_self]
  rw [CharP.intCast_eq_zero_iff k l] at h1
  have := Int.eq_zero_of_abs_lt_dvd h1 hab
  omega

theorem resCount_single {k : Type} [Field k] [DecidableEq k] (u : ℤ) (x : k) :
    resCount {u} 0 x = if (u : k) = x then 1 else 0 := by
  unfold resCount
  rw [Multiset.filter_singleton]
  simp only [sub_zero]
  split_ifs <;> simp

theorem resCount_block {k : Type} [Field k] [DecidableEq k] (w : ℤ) (t : ℕ) (x : k) :
    resCount (block w t) w x = ∑ e : Fin t, if ((e.val : ℤ) : k) = x then 1 else 0 := by
  unfold resCount
  rw [Fin.sum_univ_eq_sum_range (fun e => if ((e : ℤ) : k) = x then 1 else 0) t, Finset.sum_boole, block,
    ← Finset.filter_val, Finset.card_val, Nat.cast_id]
  symm
  refine Finset.card_bij (fun e _ => w + e) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at he ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [add_sub_cancel_left]; exact he.2
  · intro a _ b _ h
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ico] at hu
    have h : (((u - w).toNat : ℕ) : ℤ) = u - w := by omega
    refine ⟨(u - w).toNat, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [h]; exact hu.2⟩

theorem sum_eq_of_counts {k ι : Type} [Field k] [DecidableEq k] {l : ℕ} [CharP k l] (S : Finset ι) (a b : ι → ℤ)
    (lo hi : ℤ) (hl : hi - lo < l) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) (hb : ∀ i ∈ S, lo ≤ b i ∧ b i ≤ hi)
    (h : ∀ y : ℤ, lo ≤ y → y ≤ hi →
      (∑ i ∈ S, if (a i : k) = y then 1 else 0 : ℕ) = ∑ i ∈ S, if (b i : k) = y then 1 else 0) :
    ∑ i ∈ S, a i = ∑ i ∈ S, b i := by
  have key : ∀ c : ι → ℤ, (∀ i ∈ S, lo ≤ c i ∧ c i ≤ hi) → ∑ i ∈ S, c i =
      ∑ y ∈ Finset.Icc lo hi, y * ((∑ i ∈ S, if (c i : k) = y then 1 else 0 : ℕ) : ℤ) := by
    intro c hc
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi' => ?_
    rw [Finset.sum_eq_single (c i)]
    · simp
    · intro y hy hne
      rw [Finset.mem_Icc] at hy
      have := hc i hi'
      rw [if_neg, mul_zero]
      intro h'
      exact hne (eq_of_cast_eq (l := l) h' (by rw [abs_lt]; omega)).symm
    · intro h'
      exact absurd (Finset.mem_Icc.2 (hc i hi')) h'
  rw [key a ha, key b hb]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_Icc] at hy
  rw [h y hy.1 hy.2]

theorem model_of_base {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {r : ℕ}
    {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m) (h : M.Base B N) : M.Model B N := by
  refine ⟨B, N, B, LinearMap.id, LinearMap.id, h, fun _ _ => rfl, Function.injective_id, fun _ _ => rfl,
    Function.surjective_id, ?_⟩
  funext i
  simp only [DFun.push, DFun.pre, F.map_id B (M.base_obj B N h)]
  ext x
  simp

theorem model_chr_eq : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → N = M.Nχ e := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he0 het N hN
  classical
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.T.character_model_exponents_signs_senWeight F M h1 h2 h3 e he0 het N hN
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, hNe⟩ := hN
  obtain ⟨μ, hss, hsen⟩ := M.base_sen B Nb hB
  obtain ⟨s, C, L, a₀, hmod, hsimple, hss', hsum, ha₀⟩ :=
    GlobalTheory.T.exists_jordanHolder_through_line_alt F M B A₁ (M.ω ^ (-e)) j p Nb (model_of_base M B Nb hB) hj hji hp hps
  rw [← hNe] at ha₀
  obtain ⟨c, hsome, hnone, hcard⟩ := GlobalTheory.JHMatch.jh_match M.T M.ω Dt.t μ s C hsimple
    (SameFactors.trans (SameFactors.symm hss') hss)
  have hW := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3
  have htη : ∀ i, (Dt.t : ℤ) ≤ Dt.η i := by
    intro i
    obtain ⟨-, -, hG, hBd⟩ := hW i
    cases hty : Dt.ty i
    · have := hG hty; omega
    · have := hBd hty; omega
  have hC : ∀ a e', c a = some e' → C a = chr (M.ω ^ (-(e'.val : ℤ))) := fun a e' h => by
    obtain ⟨f, hf, hb⟩ := hsome a e' h
    exact eq_chr_of_bijective _ _ f hf hb
  have hch : ∀ (A : Ob k G) (Λ : Lats k n A.m) (e' : Fin Dt.t), M.Model A Λ →
      A = chr (M.ω ^ (-(e'.val : ℤ))) → ∃ κ : ZMod n → ℤ, ∀ i, |κ i| ≤ Dt.sg l i ∧
        (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧
        ∀ x, sen ((F.D A).γ i) (Λ i) x = resCount {(e'.val : ℤ) - κ i} 0 x := by
    rintro A Λ e' hm rfl
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.character_model_exponents_signs_senWeight F M h1 h2 h3 e' (by omega) (by omega) Λ hm
    exact ⟨κ, fun i => (hκ i).2⟩
  have hex : ∀ a, ∃ κ : ZMod n → ℤ, ∀ e', c a = some e' → ∀ i, |κ i| ≤ Dt.sg l i ∧
        (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧
        ∀ x, sen ((F.D (C a)).γ i) (L a i) x = resCount {(e'.val : ℤ) - κ i} 0 x := by
    intro a
    cases hc : c a with
    | none => exact ⟨0, fun _ h => by cases h⟩
    | some e' =>
      obtain ⟨κ, hκ⟩ := hch (C a) (L a) e' (hmod a) (hC a e' hc)
      exact ⟨κ, fun e'' h => by cases h; exact hκ⟩
  choose κ hκ using hex
  let cc : Fin s → ℤ := fun a => (c a).elim 0 fun e' => (e'.val : ℤ)
  let S : Finset (Fin s) := Finset.univ.filter fun a => c a ≠ none
  have hS : ∀ a ∈ S, ∃ e', c a = some e' ∧ cc a = e'.val := by
    intro a ha
    obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.1 (Finset.mem_filter.1 ha).2
    exact ⟨e', he', by simp [cc, he']⟩
  have hzero : ∀ i, ∀ a ∈ S, κ a i = 0 := by
    intro i
    have hT := h1 i
    have hη := htη i
    have hsumeq : ∑ a ∈ S, (cc a - κ a i) = ∑ a ∈ S, cc a := by
      refine sum_eq_of_counts (k := k) (l := l) S _ _ (-(Dt.sg l i : ℤ)) (Dt.t + Dt.sg l i) (by omega) ?_ ?_ ?_
      · intro a ha
        obtain ⟨e', he', hcc⟩ := hS a ha
        have := abs_le.1 (hκ a e' he' i).1
        have := e'.2
        omega
      · intro a ha
        obtain ⟨e', he', hcc⟩ := hS a ha
        have := e'.2
        omega
      · intro y hy1 hy2
        have hU : ∀ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) ≠ (y : k) := by
          intro u hu h
          refine (hW i).2.1 u hu (Dt.w i + y) (by omega) (by omega) ?_
          push_cast at h ⊢
          linear_combination h
        have e1 : (∑ a ∈ S, if ((cc a - κ a i : ℤ) : k) = y then 1 else 0 : ℕ) =
            ∑ a, sen ((F.D (C a)).γ i) (L a i) (y : k) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun a _ => ?_
          cases hc : c a with
          | none =>
            simp only [ne_eq, not_true_eq_false, if_false]
            by_contra hne
            obtain ⟨A', j', p', q1, q2, q3, q4⟩ := hnone a hc
            obtain ⟨u, hu, hux⟩ := GlobalTheory.T.senWeight_subquotient_model_mem_residues F M h1 h2 h3 A' (C a) j' p' (L a) q1 q2 q3 q4 (hmod a) i y
              (Ne.symm hne)
            exact hU u hu hux
          | some e' =>
            rw [(hκ a e' hc i).2.2.2, resCount_single, if_pos (by simp)]
            simp [cc, hc]
        have e2 : resCount (Dt.Ut i) (Dt.w i) (y : k) = resCount (block (Dt.w i) Dt.t) (Dt.w i) (y : k) := by
          unfold resCount
          rw [TopData.Ut, Multiset.filter_add, Multiset.filter_eq_nil.2 hU, zero_add]
          rfl
        rw [e1, ← hsum, hsen, e2, resCount_block, Finset.sum_filter,
          ← Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
          Fintype.sum_option, Finset.mul_sum,
          Finset.sum_eq_zero (s := Finset.univ.filter fun a => c a = none), zero_add]
        · refine Finset.sum_congr rfl fun e' _ => ?_
          rw [← hcard e', ← smul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hc := (Finset.mem_filter.1 ha).2
          simp [cc, hc]
        · intro a ha
          have hc := (Finset.mem_filter.1 ha).2
          simp [hc]
    have hs0 : ∑ a ∈ S, κ a i = 0 := by
      rw [Finset.sum_sub_distrib] at hsumeq
      linarith
    cases hty : Dt.ty (i + 1)
    · refine (Finset.sum_eq_zero_iff_of_nonneg fun a ha => ?_).1 hs0
      obtain ⟨e', he', -⟩ := hS a ha
      simpa using (hκ a e' he' (i + 1)).2.1 hty
    · refine (Finset.sum_eq_zero_iff_of_nonpos fun a ha => ?_).1 hs0
      obtain ⟨e', he', -⟩ := hS a ha
      simpa using (hκ a e' he' (i + 1)).2.2.1 hty
  have hCa : C a₀ = chr (M.ω ^ (-e)) := congrArg Sigma.fst ha₀
  have haS : a₀ ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hc => ?_⟩
    have := hnone a₀ hc
    rw [hCa] at this
    obtain ⟨A', j', p', q1, q2, q3, q4⟩ := this
    have hp0 := GlobalTheory.T.hom_to_characterLine_eq_zero F M h1 h2 h3 e (by omega) het A' j' p' q1 q2 q3
    obtain ⟨x, hx⟩ := q4 (fun _ => 1)
    rw [hp0] at hx
    simpa using congrFun hx 0
  obtain ⟨e', he', -⟩ := hS a₀ haS
  have hee : e = e'.val := by
    have hω := chr_inj (hCa.symm.trans (hC a₀ e' he'))
    have hT := h1 0
    have hη := htη 0
    have := e'.2
    by_contra hne
    refine M.ω_ne (e - e'.val).natAbs (by omega) (by omega) ?_
    have h : M.ω ^ (e - (e'.val : ℤ)) = 1 := by
      rw [sub_eq_add_neg, zpow_add, ← hω, ← zpow_add, add_neg_cancel, zpow_zero]
    exact pow_natAbs_eq_one.2 h
  funext i
  have hsen0 := congrArg (fun P : Σ A : Ob k G, Lats k n A.m =>
    sen ((F.D P.1).γ i) (P.2 i) ((e : ℤ) : k)) ha₀
  simp only at hsen0
  rw [(hκ a₀ e' he' i).2.2.2, (hκ₀ i).2.2.2.2, hzero i a₀ haS, resCount_single, resCount_single, ← hee,
    if_pos (by simp)] at hsen0
  have h0 : κ₀ i = 0 := by
    split_ifs at hsen0 with h
    have hT := h1 i
    have hb := abs_le.1 (hκ₀ i).2.1
    have := eq_of_cast_eq (l := l) h (by rw [abs_lt]; omega)
    omega
  rw [(hκ₀ i).1, h0, sh_zero_eq]

end GlobalTheory.Models.CharModel
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPhiGammaModel_character_eq_standard : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → N = M.Nχ e := by
  atlas_forward_decl GlobalTheory.Models.CharModel.model_chr_eq
end

section
noncomputable section
namespace GlobalTheory.Models.EPolyModel
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem map_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a) (g' : Vc k b →ₗ[k] Vc k b)
    (h : ∀ x, φ (g x) = g' (φ x)) (x : Vc k a) : φ (nab g x) = nab g' (φ x) := by
  rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, h]

theorem map_aeval_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (f : Polynomial k) (x : Vc k a) :
    φ (Polynomial.aeval (nab g) f x) = Polynomial.aeval (nab g') f (φ x) := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact φ.map_smul_of_tower c x
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval (nab g')), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, map_nab φ g g' h]

theorem comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ)
    (hN : EPoly g' N s) : EPoly g (N.comap (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, fun x hx => ?_⟩
  have h1 := hN (φ x) hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  change φ _ ∈ N
  rwa [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem map {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k a)) (s : ℤ)
    (hN : EPoly g N s) : EPoly g' (N.map (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hN x hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  refine ⟨_, h1, ?_⟩
  change φ _ = _ • nab g' (Polynomial.aeval (nab g') f (φ x))
  rw [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem model_ePoly : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T3 l →
    ∀ (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i, Dt.ty i = LType.Bd →
      EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h3 A N hN i hi
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have oB := M.base_obj B Nb hB
  have o1 := F.obj_sub A₁ B j hj hji oB
  have oA := F.obj_quot A₁ A p hp hps o1
  exact map _ _ _ (F.map_γ A₁ A p o1 oA hp i) _ _
    (comap _ _ _ (F.map_γ A₁ B j o1 oB hj i) _ _ (M.base_e h1 h3 B Nb hB i hi))

end GlobalTheory.Models.EPolyModel
end
end

section
section
noncomputable section
namespace GlobalTheory.TopSteps.ExtPair
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem exists_proj {m m' : ℕ} (hm : m' = m + 1) (a : (Fin m → k) →ₗ[k] (Fin m' → k)) (e : Fin m' → k)
    (ha : Function.Injective a) (he : e ∉ LinearMap.range a) :
    ∃ p : (Fin m' → k) →ₗ[k] (Fin 1 → k), Function.Exact a p ∧ p e = (fun _ => 1) ∧ Function.Surjective p := by
  obtain ⟨f, hf, hfe⟩ := LinearMap.exists_extend_of_notMem (0 : LinearMap.range a →ₗ[k] k) he 1
  have hfs : Function.Surjective f := fun c => ⟨c • e, by simp [hfe]⟩
  have hle : LinearMap.range a ≤ LinearMap.ker f := fun x hx => by
    simpa using LinearMap.congr_fun hf ⟨x, hx⟩
  have h1 := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 hfs] at h1
  have h2 := LinearMap.finrank_range_of_inj ha
  simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1 h2
  have heq : LinearMap.range a = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_eq hle (by omega)
  refine ⟨LinearMap.pi fun _ => f, fun x => ?_, funext fun _ => hfe, fun y => ?_⟩
  · change _ ↔ x ∈ LinearMap.range a
    rw [heq, LinearMap.mem_ker]
    constructor
    · intro h; exact congrFun h 0
    · intro h; exact funext fun _ => h
  · obtain ⟨x, hx⟩ := hfs (y 0)
    exact ⟨x, funext fun j => by rw [Subsingleton.elim j 0]; exact hx⟩

theorem mem_sh_comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ) (x : Vc k a) :
    x ∈ sh s (N.comap (φ.restrictScalars k⟦X⟧)) ↔ φ x ∈ sh s N := by
  rw [mem_sh_iff_smul_mem, mem_sh_iff_smul_mem, ← map_smul]; rfl

theorem aeval_nab_mem {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (N : Submodule k⟦X⟧ (Vc k a)) (hN : CondC g N)
    (f : Polynomial k) (x : Vc k a) (hx : x ∈ N) : Polynomial.aeval (nab g) f x ∈ N := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact N.smul_of_tower_mem c hx
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply]
    exact N.add_mem (hp x hx) (hq x hx)
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ ((condC_iff_nab_mem g N).1 hN x hx)

theorem aeval_nab_fixed {a : ℕ} (g : Vc k a →ₗ[k] Vc k a) (f : Polynomial k) (u : Vc k a) (hu : g u = u) :
    Polynomial.aeval (nab g) f u = f.eval 0 • u := by
  apply Module.End.aeval_apply_of_mem_apply_eq_smul
  rw [nab_apply_eq, hu, sub_self, smul_zero, zero_smul]

theorem exists_model_repr_inZZ : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l →
    ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A →
      ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A z hz
  obtain ⟨E, NE, ⟨hm, a, e, ha, hai, he, hez⟩, hNE⟩ := hz
  obtain ⟨p, hex, hpe, hps⟩ := exists_proj hm a e hai he
  have hpa : ∀ y, p (a y) = 0 := hex.apply_apply_eq_zero
  have hp : IsHom E (chr 1) p := by
    intro σ x
    obtain ⟨y, hy⟩ := (hex (x - p x 0 • e)).1 (by
      rw [map_sub, map_smul, hpe]; funext j; rw [Subsingleton.elim j 0]; simp)
    have hx : x = a y + p x 0 • e := by rw [hy]; abel
    have h : p (E.ρ σ x) = p x := by
      conv_lhs => rw [hx]
      conv_rhs => rw [hx]
      rw [map_add, map_smul, ← ha, hez]
      simp only [map_add, map_smul, hpa, add_zero]
    rw [h]
    change _ = (((1 : G →* kˣ) σ : kˣ) : k) • p x
    simp
  obtain ⟨oE, -, hAB, hC⟩ := GlobalTheory.T.obj_and_abc_of_model F M E NE hNE
  have oA := F.obj_sub A E a ha hai oE
  have o1 := F.obj_one
  have hq : M.Model (chr 1) (F.push E (chr 1) p NE) :=
    GlobalTheory.Models.ModTh.model_push_of_surjective F M E (chr 1) p NE hp hps hNE
  have hq' : ∀ χ : G →* kˣ, χ = 1 → M.Model (chr χ) (F.push E (chr 1) p NE) := by
    rintro _ rfl; exact hq
  have hpush : ∀ i, F.push E (chr 1) p NE i = Submodule.span k⟦X⟧ {F.unit i} := fun i => by
    rw [← M.χ_zero i]
    exact congrFun (GlobalTheory.T.twistedPhiGammaModel_character_eq_standard F M h1 h2 h3 0 le_rfl (by exact_mod_cast Dt.one_le_letterBlockLength) _
      (hq' _ (by simp))) i
  have hε : ∀ i, ∃ ε ∈ NE i, F.map E (chr 1) p i ε = F.unit i := fun i => by
    have : F.unit i ∈ F.push E (chr 1) p NE i := by
      rw [hpush]; exact Submodule.mem_span_singleton_self _
    exact this
  choose ε hεN hεp using hε
  have hD := GlobalTheory.Models.DFun.map_exact_middle F A E (chr 1) a p oE ha hp hai hps hex
  have hinj := F.map_inj A E a oA oE ha hai
  have aφ := F.map_φ A E a oA oE ha
  have aγ := F.map_γ A E a oA oE ha
  have pφ := F.map_φ E (chr 1) p oE o1 hp
  have pγ := F.map_γ E (chr 1) p oE o1 hp
  have hb : ∀ i, ∃ b, F.map A E a i b = (F.D E).φ i (ε (i - 1)) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pφ, hεp, hεp, F.unit_φ, sub_self])
  have hg : ∀ i, ∃ g, F.map A E a i g = (F.D E).γ i (ε i) - ε i := fun i =>
    (hD i _).1 (by rw [map_sub, pγ, hεp, F.unit_γ, sub_self])
  choose b hb using hb
  choose g hg using hg
  refine ⟨F.pre A E a NE, b, g, GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A E a NE ha hai hNE,
    ⟨E, a, p, e, ε, oE, ha, hp, hai, hex, hpe, hez, fun i => ⟨hεp i, hb i, hg i⟩⟩, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · apply hinj i
    rw [map_sub, map_sub, aφ, aγ, hb, hg, hg, map_sub, map_sub, (F.D E).comm]
    abel
  · refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hg]; exact hC i _ (hεN i)
  · intro _
    refine (mem_sh_comap _ _ _ _).2 ?_
    rw [hb]
    have hw : 1 ≤ Dt.w i := (Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2
      ⟨le_rfl, by have := Dt.one_le_letterBlockLength; omega⟩)))).1
    refine Submodule.sub_mem _ ((hAB i).1 (Submodule.subset_span ⟨_, hεN _, rfl⟩)) ?_
    apply sh_le_sh_of_le (a := 0) (by omega)
    rw [sh_zero_eq]; exact hεN i
  · intro hi
    constructor
    · have hdec : ∀ y ∈ pull ((F.D E).φ i) (NE (i - 1)), ∃ m ∈ pull ((F.D A).φ i) (F.pre A E a NE (i - 1)),
          ∃ c : k⸨X⸩, y = F.map A E a i m + c • (F.D E).φ i (ε (i - 1)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨x, hx, rfl⟩ := hy
          have h4 : F.map E (chr 1) p (i - 1) x ∈ F.push E (chr 1) p NE (i - 1) := ⟨x, hx, rfl⟩
          rw [hpush, Submodule.mem_span_singleton] at h4
          obtain ⟨c, hc⟩ := h4
          obtain ⟨m, hm⟩ := (hD (i - 1) (x - c • ε (i - 1))).1 (by
            rw [map_sub, LinearMap.map_smul_of_tower, hεp, hc, sub_self])
          have hmN : m ∈ F.pre A E a NE (i - 1) := by
            change F.map A E a (i - 1) m ∈ NE (i - 1)
            rw [hm]; exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ (hεN _))
          refine ⟨(F.D A).φ i m, Submodule.subset_span ⟨m, hmN, rfl⟩, R.φ (algebraMap k⟦X⟧ k⸨X⸩ c), ?_⟩
          rw [aφ, hm, ← (F.D E).φ_semi i, algebraMap_smul, ← map_add, sub_add_cancel]
        | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
        | add y y' _ _ hy hy' =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          obtain ⟨m', hm', c', rfl⟩ := hy'
          exact ⟨m + m', Submodule.add_mem _ hm hm', c + c', by rw [map_add, add_smul]; abel⟩
        | smul d y _ hy =>
          obtain ⟨m, hm, c, rfl⟩ := hy
          refine ⟨d • m, Submodule.smul_mem _ _ hm, d • c, ?_⟩
          rw [smul_add, LinearMap.map_smul_of_tower, smul_assoc]
      obtain ⟨m, hm, c, hc⟩ := hdec _ ((hAB i).2 (mem_sh_iff_exists.2 ⟨_, hεN i, rfl⟩))
      have h5 := congrArg (F.map E (chr 1) p i) hc
      rw [map_smul, map_add, map_smul, pφ, hεp, hεp, F.unit_φ, (hD i).apply_apply_eq_zero, zero_add] at h5
      have h6 : vv k ^ Dt.wst i = c := smul_left_injective _ (F.unit_ne i) h5
      rw [mem_sh_iff_smul_mem, neg_neg]
      have h7 : vv k ^ Dt.wst i • b i = -m := by
        apply hinj i
        rw [map_smul, hb, smul_sub, hc, h6, map_neg]; abel
      rw [h7]; exact Submodule.neg_mem _ hm
    · obtain ⟨f, hf, hfN⟩ := GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 E NE hNE i hi
      obtain ⟨x, hx⟩ := (hD i (ε i - (f.eval 0)⁻¹ • Polynomial.aeval (nab ((F.D E).γ i)) f (ε i))).1 (by
        rw [map_sub, LinearMap.map_smul_of_tower,
          EPolyModel.map_aeval_nab (F.map E (chr 1) p i) _ _ (pγ i), hεp, aeval_nab_fixed _ _ _ (F.unit_γ i),
          smul_smul, inv_mul_cancel₀ hf, one_smul, sub_self])
      refine ⟨x, ?_, (mem_sh_comap _ _ _ _).2 ?_⟩
      · change F.map A E a i x ∈ NE i
        rw [hx]
        exact Submodule.sub_mem _ (hεN i)
          (Submodule.smul_of_tower_mem _ _ (aeval_nab_mem _ _ (hC i) f _ (hεN i)))
      · have h4 := hfN _ (hεN i)
        set y := Polynomial.aeval (nab ((F.D E).γ i)) f (ε i)
        have h5 : (F.D E).γ i y - y ∈ sh (Dt.wst i + 2) (NE i) := by
          rw [show Dt.wst i + 2 = 1 + (Dt.wst i + 1) by ring, ← sh_sh_eq, mem_sh_iff_smul_mem, zpow_neg_one]
          exact h4
        have h6 : F.map A E a i (g i - ((F.D A).γ i x - x)) = (f.eval 0)⁻¹ • ((F.D E).γ i y - y) := by
          rw [map_sub, map_sub, aγ, hg, hx, map_sub, map_smul, smul_sub]; abel
        rw [h6]
        exact Submodule.smul_of_tower_mem _ _ h5

end GlobalTheory.TopSteps.ExtPair
end
end

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A : Ob k G) (z : G → Fin A.m → k), z ∈ M.twistedModelAdmissibleCocycles A → ∃ (N : Lats k n A.m) (b g : ZMod n → Vc k A.m), M.Model A N ∧ Repr F A z b g ∧ InZZ (F.D A) Dt N b g := by
  atlas_forward_decl GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ
end
