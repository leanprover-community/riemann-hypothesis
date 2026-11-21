import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeRankTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorEqZeroOfRestrictAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSectionOfCoefficientSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefSpecMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverWithLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleAllObjOfExtend

section
open TensorProduct

namespace GlobalTheory

theorem invertible_of_faithfullyFlat_baseChange_tensor_int :
    ∀ (R R' O : Type) [CommRing R] [CommRing R'] [Algebra R R'] [CommRing O] [Module.FaithfullyFlat R R'] (M : Type) [AddCommGroup M]
    [Module R M] [Module O M] [SMulCommClass R O M] (N : Type) [AddCommGroup N] [Module R' N] [Module O N]
    [SMulCommClass R' O N] (e : R' ⊗[R] M ≃ₗ[R'] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
    Module.Invertible (R' ⊗[ℤ] O) N → Module.Invertible (R ⊗[ℤ] O) M := by
  intro R R' O _ _ _ _ _ M _ _ _ _ N _ _ _ _ e he hN
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)
  letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom
  haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩
  have hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o := fun r o => rfl

  haveI : IsScalarTower R (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let l : R' →ₗ[R] R' ⊗[ℤ] O :=
    { toFun := fun r' => r' ⊗ₜ 1
      map_add' := fun x y => add_tmul x y 1
      map_smul' := fun r r' => rfl }
  let u : (R ⊗[ℤ] O) ⊗[R] R' →ₗ[R ⊗[ℤ] O] R' ⊗[ℤ] O := LinearMap.liftBaseChange _ l
  have hu : ∀ (r : R) (o : O) (r' : R'), u ((r ⊗ₜ o) ⊗ₜ r') = (algebraMap R R' r * r') ⊗ₜ o := by
    intro r o r'
    change f (r ⊗ₜ o) * (r' ⊗ₜ 1) = _
    rw [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  let w : R' →ₗ[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' :=
    LinearMap.mk₂ ℤ (fun r' o => ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r')
      (fun x y o => by simp [tmul_add])
      (fun n x o => map_zsmul (TensorProduct.mk R (R ⊗[ℤ] O) R' ((1 : R) ⊗ₜ[ℤ] o)) n x)
      (fun x o o' => by simp [tmul_add, add_tmul])
      (fun n x o => by
        change (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 (n • o)) =
          n • (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 o)
        rw [map_zsmul, map_zsmul])
  let v : R' ⊗[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' := TensorProduct.lift w
  have hv : ∀ (r' : R') (o : O), v (r' ⊗ₜ o) = ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r' := fun r' o => rfl
  have huv : ∀ y, u (v y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' o =>
      rw [hv, hu, map_one, _root_.one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hvu : ∀ x, v (u x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r' =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul r o =>
        rw [hu, ← Algebra.smul_def, hv, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
          _root_.mul_one]
      | add a b ha hb => rw [add_tmul, map_add, map_add, ha, hb]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hubij : Function.Bijective u :=
    ⟨fun a b hab => by rw [← hvu a, ← hvu b, hab], fun y => ⟨v y, huv y⟩⟩
  haveI : Module.FaithfullyFlat (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⊗[ℤ] O) ((R ⊗[ℤ] O) ⊗[R] R')
      (LinearEquiv.ofBijective u hubij).symm

  have hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m) := by
    intro a m
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r o =>
      rw [hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he,
        TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]
    | add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]
  let j : M →ₗ[R ⊗[ℤ] O] N :=
    { toFun := fun m => e (1 ⊗ₜ m)
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun a m => hj a m }
  let Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N := LinearMap.liftBaseChange _ j
  let g : R' →+ M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M :=
    AddMonoidHom.mk' (fun r' => (TensorProduct.mk (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M
      (r' ⊗ₜ[ℤ] (1 : O))).toAddMonoidHom) (by intro a b; ext m; simp [add_tmul])
  let ψ : R' ⊗[R] M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M := TensorProduct.liftAddHom g (by
    intro r r' m
    have hr : r • m = ((r ⊗ₜ[ℤ] (1 : O)) : R ⊗[ℤ] O) • m := by
      rw [TensorProduct.Algebra.smul_def, one_smul]
    simp only [g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    change _ = f (r ⊗ₜ 1) * _
    simp only [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, Algebra.smul_def])
  have h1 : ∀ y, Φ (ψ y) = e y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' m =>
      simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
        LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Φ, LinearMap.liftBaseChange_tmul]
      change (r' ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = _
      rw [TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have h2 : ∀ z, ψ (e.symm (Φ z)) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r' o =>
        have hΦ : Φ ((r' ⊗ₜ[ℤ] o) ⊗ₜ m) = e (r' ⊗ₜ (o • m)) := by
          simp only [Φ, LinearMap.liftBaseChange_tmul]
          change (r' ⊗ₜ[ℤ] o) • e (1 ⊗ₜ m) = _
          rw [TensorProduct.Algebra.smul_def, ← he, ← map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, _root_.mul_one]
        rw [hΦ, LinearEquiv.symm_apply_apply]
        simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
        have ho : o • m = (((1 : R) ⊗ₜ[ℤ] o) : R ⊗[ℤ] O) • m := by
          rw [TensorProduct.Algebra.smul_def, one_smul]
        rw [ho, ← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        change f (1 ⊗ₜ o) * _ = _
        rw [hf, map_one, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
      | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj : Function.Injective Φ := fun a b hab => by rw [← h2 a, ← h2 b, hab]
  have hsurj : Function.Surjective Φ := fun n =>
    ⟨ψ (e.symm n), by rw [h1, LinearEquiv.apply_symm_apply]⟩
  have hb : IsBaseChange (R' ⊗[ℤ] O) j :=
    IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩) fun m => by
      change Φ (1 ⊗ₜ m) = j m
      rw [LinearMap.liftBaseChange_tmul, one_smul]
  haveI := hN
  exact FlatDescent.invertible_of_isBaseChange hb

end GlobalTheory
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem span_torsion_of_indep {O : Type} [CommRing O] {G : Type} [CommGroup G] (N : ℕ)
    [Finite (O ⧸ Ideal.span {(N : O)})] (act : O → G →* G) (hone : ∀ x, act 1 x = x)
    (hmul : ∀ a b x, act (a * b) x = act b (act a x)) (hadd : ∀ a b x, act (a + b) x = act a x * act b x)
    (p q : Fin 2 → G) (hp : ∀ i, p i ^ N = 1) (hq : ∀ i, q i ^ N = 1)
    (ip : ∀ a b, act a (p 0) * act b (p 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (iq : ∀ a b, act a (q 0) * act b (q 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b)
    (sq : ∀ y, y ^ N = 1 → ∃ a b, y = act a (q 0) * act b (q 1)) :
    ∀ y, y ^ N = 1 → ∃ a b, y = act a (p 0) * act b (p 1) := by
  have hzero : ∀ x, act 0 x = 1 := fun x ↦ by
    have := hadd 0 0 x
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hnat : ∀ (n : ℕ) x, act (n : O) x = x ^ n := fun n x ↦ by
    induction n with
    | zero => simp [hzero]
    | succ n ih => rw [Nat.cast_succ, hadd, ih, hone, pow_succ]
  let f : (Fin 2 → G) → (O × O →+ Additive G) := fun r ↦ AddMonoidHom.mk'
    (fun c ↦ Additive.ofMul (act c.1 (r 0) * act c.2 (r 1))) (fun c d ↦ by
      rw [← ofMul_mul, Prod.fst_add, Prod.snd_add, hadd, hadd, _root_.mul_mul_mul_comm])
  let I : AddSubgroup O := (Ideal.span {(N : O)}).toAddSubgroup
  have hker : ∀ r : Fin 2 → G, (∀ i, r i ^ N = 1) →
      (∀ a b, act a (r 0) * act b (r 1) = 1 → (N : O) ∣ a ∧ (N : O) ∣ b) → (f r).ker = I.prod I := by
    intro r hr ir
    ext ⟨a, b⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_prod]
    change act a (r 0) * act b (r 1) = 1 ↔ a ∈ Ideal.span {(N : O)} ∧ b ∈ Ideal.span {(N : O)}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    refine ⟨ir a b, ?_⟩
    rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    rw [hmul, hmul, hnat, hnat, hr, hr, map_one, map_one, _root_.one_mul]
  have hI : I.index ≠ 0 := by
    have : Finite (O ⧸ I) := ‹Finite (O ⧸ Ideal.span {(N : O)})›
    exact AddSubgroup.index_ne_zero_of_finite
  have cp : Nat.card (f p).range = I.index * I.index := by
    rw [← AddSubgroup.index_ker, hker p hp ip, AddSubgroup.index_prod]
  have cq : Nat.card (f q).range = I.index * I.index := by
    rw [← AddSubgroup.index_ker, hker q hq iq, AddSubgroup.index_prod]
  have : Finite (f q).range := Nat.finite_of_card_ne_zero (cq ▸ mul_ne_zero hI hI)
  have hle : (f p).range ≤ (f q).range := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    obtain ⟨c, d, h⟩ := sq (act a (p 0) * act b (p 1)) (by
      rw [mul_pow, ← map_pow, ← map_pow, hp, hp, map_one, map_one, _root_.one_mul])
    exact ⟨(c, d), congrArg Additive.ofMul h.symm⟩
  have heq := AddSubgroup.eq_of_le_of_card_ge hle (by rw [cp, cq])
  intro y hy
  obtain ⟨c, d, h⟩ := sq y hy
  have hm : Additive.ofMul y ∈ (f p).range := heq ▸ ⟨(c, d), congrArg Additive.ofMul h.symm⟩
  obtain ⟨⟨a, b⟩, hab⟩ := hm
  exact ⟨a, b, (congrArg Additive.toMul hab).symm⟩

theorem nonempty_level_of_torsion_basis (hT : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (S : Scheme.{0}) (X : Obj F 𝔠 S)
    (N : ℕ) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), (N : Ω) ≠ 0 →
    ∃ p : Fin 2 → (Over.mk t ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : Over.mk t ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b)) :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (K : Type) [Field K] [IsAlgClosed K],
    (N : K) ≠ 0 → ∀ X : Obj F 𝔠 (Sp K), Nonempty (X.Level N) := by
  intro F _ _ _ 𝔠 N K _ _ hN X
  obtain ⟨p, hp, ip, -⟩ : ∃ p : Fin 2 → (𝟙_ (Over (Sp K)) ⟶ X.A), (∀ i, p i ^ N = 1) ∧
      (∀ a b : 𝓞 F, (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) = 1 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : 𝟙_ (Over (Sp K)) ⟶ X.A, y ^ N = 1 → ∃ a b : 𝓞 F, y = (p 0 ≫ X.rm.act a) * (p 1 ≫ X.rm.act b) :=
    hT F 𝔠 (Sp K) X N K (𝟙 _) hN
  have inj : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (a b : 𝓞 F),
      (toUnit (Over.mk t) ≫ p 0 ≫ X.rm.act a) * (toUnit (Over.mk t) ≫ p 1 ≫ X.rm.act b) = 1 →
        (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
    intro Ω _ _ t a b h
    apply ip
    rw [← MonObj.comp_mul, ← MonObj.comp_one (toUnit (Over.mk t))] at h
    have ht : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
    have : Epi t := inferInstance
    apply Over.OverMorphism.ext
    have h' := congrArg (fun z ↦ z.left) h
    simp only [Over.comp_left, ht] at h'
    exact (cancel_epi t).1 h'
  refine ⟨⟨p, hp, inj, fun Ω _ _ t ↦ ?_⟩⟩
  have hNΩ : (N : Ω) ≠ 0 := by
    have := (Spec.preimage t).hom.injective.ne hN
    simpa using this
  have hN0 : (N : 𝓞 F) ≠ 0 := by
    have : N ≠ 0 := by rintro rfl; simp at hN
    exact_mod_cast this
  obtain ⟨q, hq, iq, sq⟩ := hT F 𝔠 (Sp K) X N Ω t hNΩ
  have : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0)
  let act : 𝓞 F → (Over.mk t ⟶ X.A) →* (Over.mk t ⟶ X.A) := fun a ↦
    haveI := X.rm.hom a
    { toFun := fun y ↦ y ≫ X.rm.act a
      map_one' := MonObj.one_comp _
      map_mul' := fun x y ↦ MonObj.mul_comp _ _ _ }
  have key := span_torsion_of_indep N act (fun x ↦ by simp [act, X.rm.one])
    (fun a b x ↦ by simp [act, X.rm.mul]) (fun a b x ↦ by simp [act, X.rm.add, MonObj.comp_mul])
    (fun i ↦ toUnit (Over.mk t) ≫ p i) q
    (fun i ↦ by rw [← MonObj.comp_pow, hp, MonObj.comp_one]) hq
    (fun a b h ↦ inj Ω t a b (by simpa [act] using h)) iq sq
  intro y hy
  obtain ⟨a, b, h⟩ := key y hy
  exact ⟨a, b, by simpa [act] using h⟩

end GlobalTheory.RealMult
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem nonempty_level_of_isAlgClosed :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (K : Type) [Field K] [IsAlgClosed K],
    (N : K) ≠ 0 → ∀ X : Obj F 𝔠 (Sp K), Nonempty (X.Level N) :=
  nonempty_level_of_torsion_basis torsion_free_rank_two

end GlobalTheory.RealMult
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem isRapoport_of_level (hDP : GlobalTheory.Published.DelignePappasModel) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (hN : 3 ≤ N) (R : Type) [CommRing R] (hNR : IsUnit (N : R))
    (hd : IsUnit ((NumberField.discr F : ℤ) : R)) (X : Obj F 𝔠 (Sp R)) (α : X.Level N) : X.IsRapoport := by
  obtain ⟨M, s, U, α₀, hfine, -, -, -, -, -, ⟨V, hV, -, hbasic, -⟩, -, -⟩ := hDP F 𝔠 N hN
  have hNZ : IsUnit (algebraMap ℤ R (N : ℤ)) := by simpa using hNR
  let ρ : Localization.Away (N : ℤ) →+* R := IsLocalization.Away.lift (N : ℤ) hNZ
  obtain ⟨b, ⟨-, φ, hpull, -⟩, -⟩ := hfine (Sp R) (spMap ρ) X α
  have hunit : IsUnit (b.appTop ((NumberField.discr F : ℤ) : Γ(M, ⊤))) := by
    rw [map_intCast]
    have := hd.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    simpa using this
  have hpre : b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤)) = ⊤ := by
    rw [Scheme.preimage_basicOpen_top]
    exact Scheme.basicOpen_of_isUnit _ hunit
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun x K _ t ⟨p, hp⟩ Y ψ hY ↦ ?_
  have hx : b x ∈ (V : Set M) := by
    apply hbasic
    change x ∈ b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤))
    rw [hpre]; trivial
  rw [hV] at hx
  refine hx K (t ≫ b) ⟨p, ?_⟩ Y (ψ ≫ φ) (hY.comp hpull)
  rw [← hp]
  first | rfl | exact Scheme.Hom.comp_apply t b p | simp

theorem isRapoport_of_field (hDP : GlobalTheory.Published.DelignePappasModel) (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (hN : 3 ≤ N) (K : Type) [Field K] (hNK : IsUnit (N : K))
    (hd : IsUnit ((NumberField.discr F : ℤ) : K)) (X : Obj F 𝔠 (Sp K)) : X.IsRapoport := by
  let σ := algebraMap K (AlgebraicClosure K)
  obtain ⟨X', φ, h⟩ := Obj.exists_isPullBy X (spMap σ)
  have hN' : IsUnit (N : AlgebraicClosure K) := by simpa using hNK.map σ
  obtain ⟨α⟩ := nonempty_level_of_isAlgClosed F 𝔠 N (AlgebraicClosure K) hN'.ne_zero X'
  have hX' : X'.IsRapoport := isRapoport_of_level hDP F 𝔠 N hN _ hN' (by simpa using hd.map σ) X' α
  obtain ⟨e, -, he⟩ := Obj.exists_lieEquiv (R' := AlgebraicClosure K) h
  exact GlobalTheory.invertible_of_faithfullyFlat_baseChange_tensor_int K (AlgebraicClosure K) (𝓞 F) X.Lie X'.Lie e he hX'

theorem isRapoport_of_isUnit_discr : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R],
  IsUnit ((NumberField.discr F : ℤ) : R) → ∀ X : Obj F 𝔠 (Sp R), X.IsRapoport := by
  intro hDP F _ _ _ 𝔠 R _ hd X
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s K _ t _ Y φ hY ↦ ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : R →+* K, spMap σ = t := ⟨(Spec.preimage t).hom, Spec.map_preimage t⟩
  have hdK : IsUnit ((NumberField.discr F : ℤ) : K) := by simpa using hd.map σ
  by_cases h3 : (3 : K) = 0
  · have h4 : IsUnit ((4 : ℕ) : K) := by
      refine IsUnit.mk0 _ ?_
      have : ((4 : ℕ) : K) = 3 + 1 := by push_cast; ring
      rw [this, h3, zero_add]; exact one_ne_zero
    exact isRapoport_of_field hDP F 𝔠 4 (by norm_num) K h4 hdK Y
  · exact isRapoport_of_field hDP F 𝔠 3 le_rfl K (IsUnit.mk0 _ (by exact_mod_cast h3)) hdK Y

end GlobalTheory.RealMult
end
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_section_of_coefficient_spec : ∀ (M : Scheme.{0}) (R₀ R : Type) [CommRing R₀] [CommRing R] [Algebra R₀ R] (b : Sp R ⟶ M)
    (W : M.Opens) (hW : IsAffineOpen W) (x : Sp R), b x ∈ W →
    ∃ (f : R) (_ : f ∉ x.asIdeal) (g : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] Localization.Away f),
      spMap (g : R₀ ⊗[ℤ] Γ(M, W) →+* Localization.Away f) ≫ coefSpecMap hW R₀ =
        spMap (algebraMap R (Localization.Away f)) ≫ b := by
  first | exact @GlobalTheory.exists_away_factor_coefSpecMap | exact GlobalTheory.exists_away_factor_coefSpecMap | (intros; apply GlobalTheory.exists_away_factor_coefSpecMap <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RealMult.LocalGen

theorem exists_basis_away {A : Type} [CommRing A] (L : Type) [AddCommGroup L] [Module A L] [Module.Finite A L]
    [Module.Projective A L] (p : PrimeSpectrum A) (n : ℕ) (hn : Module.rankAtStalk (R := A) L p = n) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ (B : Type) [CommRing B] [Algebra A B], IsUnit (algebraMap A B g) →
      Nonempty (Module.Basis (Fin n) B (B ⊗[A] L)) := by
  haveI : Module.FinitePresentation A L := Module.finitePresentation_of_projective A L
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl L) :=
    Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (Fin n) (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl L) :=
    Module.finBasisOfFinrankEq _ _ hn
  obtain ⟨g, hg, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl L) (Localization.AtPrime p.asIdeal) b
  refine ⟨g, hg, fun B _ _ hu ↦ ?_⟩
  letI : Algebra (Localization (Submonoid.powers g)) B := (IsLocalization.Away.lift g hu).toAlgebra
  haveI : IsScalarTower A (Localization (Submonoid.powers g)) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq g hu a).symm
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization (Submonoid.powers g))
    (LocalizedModule.mkLinearMap (Submonoid.powers g) L)).equiv
  exact ⟨((b'.map e.symm).baseChange B).map
    (AlgebraTensorModule.cancelBaseChange A (Localization (Submonoid.powers g)) B B L)⟩

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem nonempty_detGen_of_basis {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))
    (b : Module.Basis (Fin (Module.finrank ℚ F)) R X.Lie) : Nonempty X.DetGen := by
  refine ⟨⟨b.det, Submodule.eq_top_iff'.2 fun f ↦ ?_⟩⟩
  rw [f.eq_smul_basis_det b]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_detGen_away {A : Type} [CommRing A] (Y : Obj F 𝔠 (Sp A)) (p : PrimeSpectrum A) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ (B : Type) [CommRing B] (σ : A →+* B), IsUnit (σ g) →
      ∀ (X : Obj F 𝔠 (Sp B)) (φ : X.A.left ⟶ Y.A.left), X.IsPullBy Y (spMap σ) φ → Nonempty X.DetGen := by
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank Y
  obtain ⟨g, hg, H⟩ := exists_basis_away Y.Lie p _ (hrk p)
  refine ⟨g, hg, fun B _ σ hu X φ h ↦ ?_⟩
  letI := σ.toAlgebra
  obtain ⟨b⟩ := H B hu
  obtain ⟨e, -⟩ := Obj.exists_lieEquiv (R' := B) h
  exact nonempty_detGen_of_basis X (b.map e)

theorem exists_affine_detGen (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M)
    (R₀ : Type) [CommRing R₀] (m : M) : ∃ (W : M.Opens) (hW : IsAffineOpen W), m ∈ W ∧
      ∀ (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
        X.IsPullBy U (coefSpecMap hW R₀) φ → Nonempty X.DetGen := by
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hm, -⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ m) isOpen_univ
  replace hW₀ : IsAffineOpen W₀ := hW₀
  obtain ⟨Y, ψ, hY⟩ := Obj.exists_isPullBy (S' := Sp Γ(M, W₀)) U hW₀.fromSpec
  obtain ⟨g, hg, H⟩ := exists_detGen_away Y (hW₀.primeIdealOf ⟨m, hm⟩)
  refine ⟨M.basicOpen g, hW₀.basicOpen g, ?_, fun X φ h ↦ ?_⟩
  · have h1 : hW₀.primeIdealOf ⟨m, hm⟩ ∈ hW₀.fromSpec ⁻¹ᵁ M.basicOpen g := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hW₀.fromSpec (hW₀.primeIdealOf ⟨m, hm⟩) ∈ M.basicOpen g := h1
    rwa [hW₀.fromSpec_primeIdealOf] at h2
  · let ρ : Γ(M, W₀) ⟶ Γ(M, M.basicOpen g) := M.presheaf.map (homOfLE (M.basicOpen_le g)).op
    let j := (Algebra.TensorProduct.includeRight :
      Γ(M, M.basicOpen g) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, M.basicOpen g)).toRingHom
    have e : coefSpecMap (hW₀.basicOpen g) R₀ = spMap (j.comp ρ.hom) ≫ hW₀.fromSpec := by
      rw [coefSpecMap, ← hW₀.map_fromSpec (hW₀.basicOpen g) (homOfLE (M.basicOpen_le g)).op, ← Category.assoc]
      congr 1
      exact (Spec.map_comp ρ (CommRingCat.ofHom j)).symm
    rw [e] at h
    obtain ⟨χ, hχ, -⟩ := h.cancel hY
    exact H _ (j.comp ρ.hom) ((M.toRingedSpace.isUnit_res_basicOpen g).map j) X χ hχ

end GlobalTheory.RealMult.LocalGen
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_generator_locally_exists : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M)
    (R₀ : Type) [CommRing R₀] (m : M), ∃ (W : M.Opens) (hW : IsAffineOpen W), m ∈ W ∧
      ∀ (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
        X.IsPullBy U (coefSpecMap hW R₀) φ → Nonempty X.DetGen := by
  atlas_forward_decl GlobalTheory.RealMult.LocalGen.exists_affine_detGen
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem spMap_restrict_comp_coefSpecMap : ∀ (M : Scheme.{0}) (W W' : M.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (R₀ : Type) [CommRing R₀],
    spMap (Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE hle).op).hom.toIntAlgHom :
      R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W')).toRingHom ≫ coefSpecMap hW R₀ = coefSpecMap hW' R₀ := by
  intro M W W' hW hW' hle R₀ _
  unfold coefSpecMap spMap
  rw [← hW.map_fromSpec hW' (homOfLE hle).op, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2

end GlobalTheory.RealMult
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_spec_restriction_compatible : ∀ (M : Scheme.{0}) (W W' : M.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (R₀ : Type) [CommRing R₀],
    spMap (Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE hle).op).hom.toIntAlgHom :
      R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W')).toRingHom ≫ coefSpecMap hW R₀ = coefSpecMap hW' R₀ := by
  atlas_forward_decl GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.QUniq

theorem eq_of_loc_two_three (R : Type) [CommRing R] (x y : R)
    (h2 : algebraMap R (Localization.Away (2 : R)) x = algebraMap R (Localization.Away (2 : R)) y)
    (h3 : algebraMap R (Localization.Away (3 : R)) x = algebraMap R (Localization.Away (3 : R)) y) : x = y := by
  rw [← sub_eq_zero]
  rw [← sub_eq_zero, ← map_sub] at h2 h3
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (2 : R)) _ _).1 h2
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (3 : R)) _ _).1 h3
  have hc : IsCoprime ((2 : R) ^ n) ((3 : R) ^ m) := by
    have : IsCoprime (2 : R) 3 := ⟨-1, 1, by norm_num⟩
    exact this.pow
  obtain ⟨a, b, hab⟩ := hc
  simp only at hn hm
  calc x - y = (a * 2 ^ n + b * 3 ^ m) * (x - y) := by rw [hab, _root_.one_mul]
    _ = a * (2 ^ n * (x - y)) + b * (3 ^ m * (x - y)) := by ring
    _ = 0 := by rw [hn, hm]; ring

theorem eq_of_loc_away (R : Type) [CommRing R] (f : PrimeSpectrum R → R) (hf : ∀ p, f p ∉ p.asIdeal)
    (x y : R) (h : ∀ p, algebraMap R (Localization.Away (f p)) x = algebraMap R (Localization.Away (f p)) y) :
    x = y := by
  rw [← sub_eq_zero]
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R R (x - y))
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hI
    let p : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hp := h p
    rw [← sub_eq_zero, ← map_sub] at hp
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f p)) _ _).1 hp
    have hmem : f p ^ n ∈ I := by
      simp only [I, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
      exact hn
    exact hf p (hq.isPrime.mem_of_pow_mem n (hIq hmem))
  have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem isRapoport_of_range_subset {M : Scheme.{0}} (U : Obj F 𝔠 M) {A : Type} [CommRing A] (c : Sp A ⟶ M)
    (X : Obj F 𝔠 (Sp A)) (φ : X.A.left ⟶ U.A.left) (hX : X.IsPullBy U c φ) (hr : Set.range c ⊆ U.rapLocus) :
    X.IsRapoport := by
  rw [Obj.isRapoport_iff]
  refine Set.eq_univ_of_forall fun s ↦ ?_
  intro K _ t hs Y ψ hY
  obtain ⟨p, rfl⟩ := hs
  exact hr ⟨t p, rfl⟩ K (t ≫ c) ⟨p, rfl⟩ Y (ψ ≫ φ) (hY.comp hX)

theorem agreeAt_on_model : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (N : ℕ) (M : Scheme.{0})
    (sM : M ⟶ Sp (Localization.Away (N : ℤ))) (U : Obj F 𝔠 M) (V : M.Opens), (V : Set M) = U.rapLocus → Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W) (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
      X.IsPullBy U (coefSpecMap hW R₀) φ → r.AgreeAt s X := by
  intro F _ _ 𝔠 N M sM U V hV hflat hnorm hcod R₀ _ k r s hrap W hW X φ hX δ
  rw [← sub_eq_zero]
  have key : TensorProduct.comm ℤ R₀ Γ(M, W) (r.val _ X trivial δ - s.val _ X trivial δ) = 0 := by
    refine rTensor_eq_zero_of_restrict_affine_inf N M sM V hflat hnorm hcod W hW R₀ _ fun W' hW' hle ↦ ?_
    let ρ : R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W') :=
      Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom.toIntAlgHom
    obtain ⟨X', φ', hX'⟩ := Obj.exists_isPullBy X (spMap ρ.toRingHom)
    obtain ⟨δ', hδ', -⟩ := Obj.IsPullBy.existsUnique_detGen (R := R₀ ⊗[ℤ] Γ(M, W)) (R' := R₀ ⊗[ℤ] Γ(M, W')) _ hX' δ
    have hU : X'.IsPullBy U (coefSpecMap hW' R₀) (φ' ≫ φ) := by
      rw [← GlobalTheory.T.coefficient_spec_restriction_compatible M W W' hW hW' (hle.trans inf_le_left) R₀]; exact hX'.comp hX
    have hrng : Set.range (coefSpecMap hW' R₀) ⊆ U.rapLocus := by
      rintro _ ⟨y, rfl⟩
      rw [← hV]
      have : (coefSpecMap hW' R₀) y ∈ Set.range hW'.fromSpec := ⟨_, rfl⟩
      rw [hW'.range_fromSpec] at this
      exact (hle.trans inf_le_right) this
    have hrX' := isRapoport_of_range_subset U _ X' _ hU hrng
    have e := hrap _ X' hrX' δ'
    rw [r.baseChange _ _ ρ X trivial X' trivial φ' δ δ' hX' hδ', s.baseChange _ _ ρ X trivial X' trivial φ' δ δ' hX' hδ',
      ← sub_eq_zero, ← map_sub] at e
    have hcomm : ∀ h, LinearMap.rTensor R₀
        (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom.toAddMonoidHom.toIntLinearMap
        (TensorProduct.comm ℤ R₀ Γ(M, W) h) =
          TensorProduct.comm ℤ R₀ Γ(M, W') (ρ h) := by
      intro h
      induction h using TensorProduct.induction_on with
      | zero => simp
      | tmul a g => rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hcomm, e, map_zero]
  exact (TensorProduct.comm ℤ R₀ Γ(M, W)).map_eq_zero_iff.1 key

end GlobalTheory.RealMult.QUniq

namespace GlobalTheory.RealMult.QUniq

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem agreeAt_of_one (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    (δ₀ : X.DetGen) (h : r.val R X trivial δ₀ = s.val R X trivial δ₀) : r.AgreeAt s X := by
  intro δ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (δ.2.symm ▸ Submodule.mem_top : δ₀.1 ∈ Submodule.span R {δ.1})
  rw [← r.homog R X trivial δ δ₀ c hc.symm, ← s.homog R X trivial δ δ₀ c hc.symm, h]

theorem agreeAt_of_inj (r s : Rule (trivialObjectCondition 𝔠) R₀ k) {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R))
    {J : Type} (R' : J → Type) [∀ i, CommRing (R' i)] [∀ i, Algebra R₀ (R' i)] (σ : ∀ i, R →ₐ[R₀] R' i)
    (hinj : ∀ x y : R, (∀ i, σ i x = σ i y) → x = y)
    (h : ∀ i (X' : Obj F 𝔠 (Sp (R' i))) (φ : X'.A.left ⟶ X.A.left),
      X'.IsPullBy X (spMap (σ i : R →+* R' i)) φ → r.AgreeAt s X') : r.AgreeAt s X := by
  intro δ
  refine hinj _ _ fun i ↦ ?_
  obtain ⟨X', φ, hX'⟩ := Obj.exists_isPullBy X (spMap (σ i : R →+* R' i))
  obtain ⟨δ', hδ', -⟩ := hX'.existsUnique_detGen (σ i : R →+* R' i) δ
  have e1 := r.baseChange R (R' i) (σ i) X trivial X' trivial φ δ δ' hX' hδ'
  have e2 := s.baseChange R (R' i) (σ i) X trivial X' trivial φ δ δ' hX' hδ'
  change r.val (R' i) X' trivial δ' = (σ i : R →+* R' i) _ at e1
  change s.val (R' i) X' trivial δ' = (σ i : R →+* R' i) _ at e2
  have := h i X' φ hX' δ'
  simpa [e1, e2] using this

end GlobalTheory.RealMult.QUniq

namespace GlobalTheory.RealMult.QUniq

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {𝔠 : FracId F} {R₀ : Type} [CommRing R₀] {k : ℕ}

theorem agreeAt_of_level (hDP : GlobalTheory.Published.DelignePappasModel) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    (N : ℕ) (hN : 3 ≤ N) {R : Type} [CommRing R] [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R))
    (α : X.Level N) : r.AgreeAt s X := by
  obtain ⟨M, sM, U, αU, hfine, -, -, -, hflat, -, ⟨V, hV, -, -, hcod⟩, hnorm, -⟩ := hDP F 𝔠 N hN
  let t : Sp R ⟶ Sp (Localization.Away (N : ℤ)) :=
    spMap (IsLocalization.Away.lift (S := Localization.Away (N : ℤ)) (N : ℤ) (g := Int.castRingHom R) (by simpa using hu))
  obtain ⟨b, ⟨-, φ, hφ, -⟩, -⟩ := hfine (Sp R) t X α
  have hmod := agreeAt_on_model F 𝔠 N M sM U V hV hflat hnorm hcod R₀ k r s hrap
  choose W hW hmW hgen using fun x : Sp R ↦ GlobalTheory.T.determinant_generator_locally_exists F 𝔠 M U R₀ (b x)
  choose f hf g hg using fun x : Sp R ↦ GlobalTheory.T.local_section_of_coefficient_spec M R₀ R b (W x) (hW x) x (hmW x)
  refine agreeAt_of_inj r s X (fun x : Sp R ↦ Localization.Away (f x)) (fun x ↦ IsScalarTower.toAlgHom R₀ R _)
    (eq_of_loc_away R f hf) fun x X' φ' hX' ↦ ?_
  obtain ⟨UW, φW, hUW⟩ := Obj.exists_isPullBy U (coefSpecMap (hW x) R₀)
  obtain ⟨δW⟩ := hgen x UW φW hUW
  have h1 : X'.IsPullBy U (spMap (g x : _ →+* _) ≫ coefSpecMap (hW x) R₀) (φ' ≫ φ) := by
    rw [hg x]; exact hX'.comp hφ
  obtain ⟨ψ, hψ, -⟩ := h1.cancel hUW
  obtain ⟨δ', hδ', -⟩ := Obj.IsPullBy.existsUnique_detGen (R := R₀ ⊗[ℤ] Γ(M, W x)) (R' := Localization.Away (f x)) _ hψ δW
  refine agreeAt_of_one r s X' δ' ?_
  rw [r.baseChange _ _ (g x) UW trivial X' trivial ψ δW δ' hψ hδ',
    s.baseChange _ _ (g x) UW trivial X' trivial ψ δW δ' hψ hδ', hmod (W x) (hW x) UW φW hUW δW]

theorem agreeAt_of_unit (hDP : GlobalTheory.Published.DelignePappasModel) (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    (N : ℕ) (hN : 3 ≤ N) {R : Type} [CommRing R] [Algebra R₀ R] (hu : IsUnit (N : R)) (X : Obj F 𝔠 (Sp R)) :
    r.AgreeAt s X := by
  obtain ⟨R', _, σ, X', φ, hff, hX', ⟨α⟩⟩ := hlev F 𝔠 N (by omega) R hu X
  letI : Algebra R₀ R' := (σ.comp (algebraMap R₀ R)).toAlgebra
  let σ' : R →ₐ[R₀] R' := { σ with commutes' := fun _ ↦ rfl }
  refine agreeAt_of_inj r s X (fun _ : Unit ↦ R') (fun _ ↦ σ') (fun x y h ↦ hff.injective (h ()))
    fun _ X'' φ'' hX'' ↦ ?_
  have h2 : X''.IsPullBy X (𝟙 _ ≫ spMap σ) φ'' := by rw [Category.id_comp]; exact hX''
  obtain ⟨ψ, hψ, -⟩ := h2.cancel hX'
  obtain ⟨α'', -⟩ := hψ.exists_level α
  exact agreeAt_of_level hDP r s hrap N hN (by simpa using hu.map σ) X'' α''

theorem agreeAt_all (hDP : GlobalTheory.Published.DelignePappasModel) (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) (r s : Rule (trivialObjectCondition 𝔠) R₀ k)
    (hrap : ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → r.AgreeAt s X)
    {R : Type} [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) : r.AgreeAt s X := by
  refine agreeAt_of_inj r s X (fun b : Bool ↦ Localization.Away (if b then (2 : R) else 3))
    (fun b ↦ IsScalarTower.toAlgHom R₀ R _) (fun x y h ↦ eq_of_loc_two_three R x y (h true) (h false)) fun b X' φ' hX' ↦ ?_
  cases b
  · have h3 : IsUnit (algebraMap R (Localization.Away (3 : R)) 3) := IsLocalization.Away.algebraMap_isUnit 3
    have h3' : IsUnit ((3 : ℕ) : Localization.Away (3 : R)) := by
      rw [Nat.cast_ofNat, ← map_ofNat (algebraMap R (Localization.Away (3 : R))) 3]; exact h3
    exact agreeAt_of_unit hDP hlev r s hrap 3 le_rfl h3' X'
  · have h2 : IsUnit (algebraMap R (Localization.Away (2 : R)) 2) := IsLocalization.Away.algebraMap_isUnit 2
    have h4 : ((4 : ℕ) : Localization.Away (2 : R)) = algebraMap R _ 2 * algebraMap R _ 2 := by
      rw [← map_mul, show (2 : R) * 2 = 4 by norm_num, map_ofNat, Nat.cast_ofNat]
    exact agreeAt_of_unit hDP hlev r s hrap 4 (by norm_num) (by rw [h4]; exact h2.mul h2) X'

end GlobalTheory.RealMult.QUniq

theorem GlobalTheory.RealMult.rule_eq_of_agree_rapoport_of_level (hlev : (∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N))) : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀]
  (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → ∀ δ : X.DetGen,
    r.val R X trivial δ = s.val R X trivial δ) → r = s := by
  intro hDP F _ _ _ 𝔠 R₀ _ k r s h
  apply Rule.ext
  funext R _ _ X hX δ
  exact QUniq.agreeAt_all hDP hlev r s h X δ
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RealMult.rule_eq_of_agree_rapoport : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀]
  (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → ∀ δ : X.DetGen,
    r.val R X trivial δ = s.val R X trivial δ) → r = s :=
  GlobalTheory.RealMult.rule_eq_of_agree_rapoport_of_level GlobalTheory.RealMult.exists_faithfullyFlat_level
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult

theorem qExpansionOnAll_of_model (hDP : GlobalTheory.Published.DelignePappasModel) (hQ : GlobalTheory.Published.HilbertQExpansion) :
    QExpansionOnAll := by
  intro F _ _ _ hf e 𝔞 𝔟 k R₀ g a hg ha haR
  obtain ⟨r₀, hr₀, hr₀u⟩ := hQ F hf e 𝔞 𝔟 k R₀ g a hg ha haR
  have hrap : ∀ (R : Type) [CommRing R] [Algebra ℂ R] (X : Obj F (𝔞 * 𝔟⁻¹) (Sp R)), X.IsRapoport := by
    intro R _ _ X
    apply isRapoport_of_isUnit_discr hDP F (𝔞 * 𝔟⁻¹) R
    have h0 : ((NumberField.discr F : ℤ) : R) = algebraMap ℂ R ((NumberField.discr F : ℤ) : ℂ) := by simp
    rw [h0]
    exact (IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _
  let r₁ : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) ℂ k :=
    { val := fun R _ _ X _ δ ↦ (r₀.extend ℂ).val R X (hrap R X) δ
      homog := fun R _ _ X _ δ δ' c h ↦ (r₀.extend ℂ).homog R X (hrap R X) δ δ' c h
      baseChange := fun R R' _ _ _ _ σ X _ X' _ φ δ δ' h h' ↦
        (r₀.extend ℂ).baseChange R R' σ X (hrap R X) X' (hrap R' X') φ δ δ' h h' }
  obtain ⟨r, hr⟩ := exists_rule_allObj_of_extend hDP F (𝔞 * 𝔟⁻¹) R₀ ℂ Subtype.val_injective k r₀ r₁ (fun R _ _ X hX δ ↦ rfl)
  have hrr : r.HasValues e 𝔞 𝔟 g := by
    intro z hz X _ δ hXz
    rw [hr ℂ X (hrap ℂ X) δ]
    exact hr₀ z hz X (hrap ℂ X) δ hXz
  refine ⟨r, hrr, ?_⟩
  intro s hs
  have hres : ∀ t : Rule (trivialObjectCondition (𝔞 * 𝔟⁻¹)) R₀ k, t.HasValues e 𝔞 𝔟 g →
      (t.restrict (Q' := rapObj (𝔞 * 𝔟⁻¹)) (fun _ _ _ _ ↦ trivial)).HasValues e 𝔞 𝔟 g :=
    fun t ht z hz X _ δ hXz ↦ ht z hz X trivial δ hXz
  have h1 := hr₀u _ (hres s hs)
  have h2 := hr₀u _ (hres r hrr)
  apply rule_eq_of_agree_rapoport hDP F (𝔞 * 𝔟⁻¹) R₀ k s r
  intro R _ _ X hX δ
  exact congrArg (fun t : Rule (rapObj (𝔞 * 𝔟⁻¹)) R₀ k ↦ t.val R X hX δ) (h1.trans h2.symm)

end GlobalTheory.RealMult
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qexpansion_on_all_components : GlobalTheory.Published.DelignePappasModel → GlobalTheory.Published.HilbertQExpansion → GlobalTheory.RealMult.QExpansionOnAll := by
  atlas_forward_decl GlobalTheory.RealMult.qExpansionOnAll_of_model
end
