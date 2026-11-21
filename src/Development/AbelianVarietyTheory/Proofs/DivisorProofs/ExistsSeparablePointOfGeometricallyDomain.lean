import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedAdjoin
import BuildAid.ForwardExisting

section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_finite_separable_point_of_separableClosure_point :
    ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B →
      Nonempty (B →ₐ[k] SeparableClosure k) →
      ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB ⟨φ⟩
  classical
  obtain ⟨t, ht⟩ := hB.out
  let K : IntermediateField k (SeparableClosure k) :=
    IntermediateField.adjoin k (φ '' (t : Set B))
  have hfin : (φ '' (t : Set B)).Finite := t.finite_toSet.image φ
  haveI : Finite (φ '' (t : Set B)) := hfin.to_subtype
  have hfd : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsSeparable.isSeparable k x).isIntegral)
  have hsep : Algebra.IsSeparable k K := Algebra.IsSeparable.of_algHom k (SeparableClosure k) K.val
  have hmem : ∀ b, φ b ∈ K.toSubalgebra := by
    intro b
    apply IntermediateField.algebra_adjoin_le_adjoin
    rw [← AlgHom.map_adjoin, ht]
    exact ⟨b, trivial, rfl⟩
  exact ⟨K, inferInstance, inferInstance, hfd, hsep, ⟨φ.codRestrict K.toSubalgebra hmem⟩⟩

end GlobalTheory

alias _root_.GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' := _root_.GlobalTheory.exists_finite_separable_point_of_separableClosure_point
end

section
section
open scoped TensorProduct

namespace GlobalTheory

theorem linearIndepOn_pow_of_isDomain_tensor_purelyInseparable (k B : Type) [Field k] [CommRing B]
    [IsDomain B] [Algebra k B] (p : ℕ) (hp : p.Prime) (hk : CharP k p)
    (hdom : ∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K →
      IsPurelyInseparable k K → IsDomain (K ⊗[k] B))
    (s : Finset (FractionRing B)) (hs : LinearIndepOn k _root_.id (s : Set (FractionRing B))) :
    LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  classical
  haveI : ExpChar k p := ExpChar.prime hp
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors B) s
  have hb : ∀ x : (s : Set (FractionRing B)), ∃ b : B,
      algebraMap B (FractionRing B) b = (d : B) • (x : FractionRing B) := fun x => hd x x.2
  choose b hb using hb
  have hinj := IsFractionRing.injective B (FractionRing B)
  have hd0 : algebraMap B (FractionRing B) (d : B) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  let φ := IsScalarTower.toAlgHom k B (FractionRing B)
  have hφ : ∀ x, φ x = algebraMap B (FractionRing B) x := fun _ => rfl
  have hb' : ∀ x, φ (b x) = algebraMap B (FractionRing B) (d : B) * (x : FractionRing B) := by
    intro x; rw [hφ, hb, Algebra.smul_def]

  have hbli : LinearIndependent k b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine Fintype.linearIndependent_iff.1 hs g ?_ i
    have h2 : φ (∑ j, g j • b j) = 0 := by rw [hg, map_zero]
    simp only [map_sum, map_smul, hb'] at h2
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (g j) _ _).symm, ← Finset.mul_sum] at h2
    exact (mul_eq_zero.1 h2).resolve_left hd0
  unfold LinearIndepOn
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hcB : ∑ j, c j • b j ^ p = 0 := by
    apply hinj
    rw [map_zero, ← hφ]
    simp only [map_sum, map_smul, map_pow, hb', mul_pow]
    rw [Finset.sum_congr rfl fun j _ => (mul_smul_comm (c j) _ _).symm, ← Finset.mul_sum]
    simp only [] at hc
    rw [hc, mul_zero]

  have hroot : ∀ j, ∃ y : AlgebraicClosure k, y ^ p = algebraMap k (AlgebraicClosure k) (c j) :=
    fun j => IsAlgClosed.exists_pow_nat_eq _ hp.pos
  choose y hy using hroot
  let K := IntermediateField.adjoin k (Set.range y)
  haveI hfin : FiniteDimensional k K :=
    IntermediateField.finiteDimensional_adjoin fun z _ => Algebra.IsIntegral.isIntegral z
  have hpi : IsPurelyInseparable k K := by
    refine (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k (AlgebraicClosure k) p).2 ?_
    rintro z ⟨j, rfl⟩
    exact ⟨1, by rw [pow_one, hy]; exact ⟨c j, rfl⟩⟩
  haveI := hdom K hfin hpi
  haveI : CharP (K ⊗[k] B) p :=
    charP_of_injective_algebraMap (algebraMap k (K ⊗[k] B)).injective p
  haveI : ExpChar (K ⊗[k] B) p := ExpChar.prime hp
  let y' := fun j => (⟨y j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩ : K)
  have hy' : ∀ j, y' j ^ p = algebraMap k K (c j) := by
    intro j; apply Subtype.ext; simp [y', hy]
  have hz : (∑ j, y' j ⊗ₜ[k] b j) ^ p = 0 := by
    rw [sum_pow_char]
    simp only [Algebra.TensorProduct.tmul_pow, hy', Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, hcB, TensorProduct.tmul_zero]
  have hz0 : ∑ j, y' j • ((1 : K) ⊗ₜ[k] b j) = 0 := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact pow_eq_zero_iff hp.ne_zero |>.1 hz
  have hli := Module.Flat.linearIndependent_one_tmul (S := K) hbli
  have hyi : y' i = 0 := Fintype.linearIndependent_iff.1 hli y' hz0 i
  have : algebraMap k (AlgebraicClosure k) (c i) = 0 := by
    rw [← hy]
    have : y i = 0 := congrArg Subtype.val hyi
    rw [this, zero_pow hp.ne_zero]
  exact (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).1 this

end GlobalTheory
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  atlas_forward_decl GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable
end

section
section
namespace GlobalTheory

open Polynomial

theorem extend_alg_hom_adjoin_integral_root :
    ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω]
    (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ →
    ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 →
    ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω,
      ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))),
        ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  intro k F Ω _ _ _ _ _ R _ θ hθ ev r hr
  let S : Subalgebra R F := Algebra.adjoin R {θ}
  let e : AdjoinRoot (minpoly R θ) ≃ₐ[R] S := minpoly.equivAdjoin hθ
  let φ : S →+* Ω := (AdjoinRoot.lift (ev : R →+* Ω) r hr).comp (e.symm : S →+* AdjoinRoot (minpoly R θ))
  have hφ : ∀ (x : F) (hx : x ∈ R) (hxS : x ∈ S), φ ⟨x, hxS⟩ = ev ⟨x, hx⟩ := by
    intro x hx hxS
    have h1 : (⟨x, hxS⟩ : S) = algebraMap R S ⟨x, hx⟩ := rfl
    simp only [φ, RingHom.comp_apply, h1]
    rw [show (e.symm : S →+* AdjoinRoot (minpoly R θ)) (algebraMap R S ⟨x, hx⟩)
        = AdjoinRoot.of (minpoly R θ) ⟨x, hx⟩ from e.symm.commutes _]
    exact AdjoinRoot.lift_of hr
  have hle : Algebra.adjoin k (insert θ (R : Set F)) ≤ S.restrictScalars k := by
    rw [Algebra.adjoin_le_iff, Set.insert_subset_iff]
    refine ⟨?_, ?_⟩
    · show θ ∈ S
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    · intro y hy
      show y ∈ S
      exact S.algebraMap_mem (⟨y, hy⟩ : R)
  have hmem : ∀ z : Algebra.adjoin k (insert θ (R : Set F)), (z : F) ∈ S := fun z => hle z.2
  let ψ₀ : Algebra.adjoin k (insert θ (R : Set F)) →+* Ω :=
    { toFun := fun z => φ ⟨z.1, hmem z⟩
      map_one' := φ.map_one
      map_mul' := fun a b => φ.map_mul ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩
      map_zero' := φ.map_zero
      map_add' := fun a b => φ.map_add ⟨a.1, hmem a⟩ ⟨b.1, hmem b⟩ }
  refine ⟨{ ψ₀ with commutes' := fun c => ?_ }, fun x hx hx' => hφ x hx (hle hx')⟩
  exact (hφ (algebraMap k F c) (R.algebraMap_mem c) _).trans (ev.commutes c)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (R : Subalgebra k F) [IsIntegrallyClosed R] (θ : F), IsIntegral R θ → ∀ (ev : R →ₐ[k] Ω) (r : Ω), Polynomial.eval₂ (ev : R →+* Ω) r (minpoly R θ) = 0 → ∃ ψ : Algebra.adjoin k (insert θ (R : Set F)) →ₐ[k] Ω, ∀ (x : F) (hx : x ∈ R) (hx' : x ∈ Algebra.adjoin k (insert θ (R : Set F))), ψ ⟨x, hx'⟩ = ev ⟨x, hx⟩ := by
  atlas_forward_decl GlobalTheory.extend_alg_hom_adjoin_integral_root
end

section
namespace GlobalTheory.AdjoinAlgebraHomNonempty

theorem nonempty_algHom_adjoin (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hh : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  have h0 : h ≠ 0 := fun e => hh (by rw [e, map_zero])
  have h0F : (h : F) ≠ 0 := fun e => h0 (Subtype.ext e)
  have hu : ∀ y : Submonoid.powers h, IsUnit (S.val y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ h0F).pow n
  have hv : ∀ y : Submonoid.powers h, IsUnit (ψ y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ hh).pow n
  let f : Localization.Away h →ₐ[k] F := IsLocalization.liftAlgHom (M := Submonoid.powers h) hu
  let g : Localization.Away h →ₐ[k] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers h) hv
  have hf : ∀ s : S, f (algebraMap S (Localization.Away h) s) = (s : F) := fun s => by
    simp [f, IsLocalization.liftAlgHom_apply]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers h) z
    have h1 := congrArg f hab
    rw [map_mul, hz, zero_mul, hf] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at hab
    exact (IsLocalization.map_units (Localization.Away h) b).mul_left_eq_zero.mp hab
  have hle : Algebra.adjoin k T ≤ f.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Localization.Away h)
      (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
    refine ⟨(↑u⁻¹ : Localization.Away h) * algebraMap S _ ⟨_, hT x hx⟩, ?_⟩
    apply mul_left_cancel₀ h0F
    have e : f u = (h : F) := by rw [hu']; exact hf h
    change (h : F) * f _ = _
    rw [map_mul, hf, ← mul_assoc]
    have e2 : (h : F) * f (↑u⁻¹ : Localization.Away h) = 1 := by
      rw [← e, ← map_mul, Units.mul_inv, map_one]
    rw [e2, one_mul]
  exact ⟨(g.comp (AlgEquiv.ofInjective f hinj).symm.toAlgHom).comp (Subalgebra.inclusion hle)⟩

end GlobalTheory.AdjoinAlgebraHomNonempty
end

section
section
namespace GlobalTheory

theorem adjoin_hom_extend_of_denominator (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hψ : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  first
  | exact @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin
  | (apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AdjoinAlgebraHomNonempty.nonempty_algHom_adjoin ..)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S), ψ h ≠ 0 → ∀ T : Set F, (∀ x ∈ T, (h : F) * x ∈ S) → Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  atlas_forward_decl GlobalTheory.adjoin_hom_extend_of_denominator
end

section
section
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

namespace GlobalTheory.SepPoint

theorem exists_clear_poly {k F : Type} [Field k] [Field F] [Algebra k F] (s : Set F)
    (p : (IntermediateField.adjoin k s)[X]) :
    ∃ q : (Algebra.adjoin k s)[X], ∃ b : Algebra.adjoin k s, b ≠ 0 ∧
      q.map (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s)) =
        C (algebraMap (Algebra.adjoin k s) (IntermediateField.adjoin k s) b) * p := by
  obtain ⟨b, hb, h⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Algebra.adjoin k s)) p
  refine ⟨IsLocalization.integerNormalization (nonZeroDivisors (Algebra.adjoin k s)) p, b,
    nonZeroDivisors.ne_zero hb, ?_⟩
  rw [h, ← IsScalarTower.algebraMap_smul (IntermediateField.adjoin k s) b p, Polynomial.smul_eq_C_mul]

theorem aeval_mem_adjoin_insert {k F : Type} [Field k] [Field F] [Algebra k F]
    (R : Subalgebra k F) (θ : F) (g : R[X]) :
    aeval θ g ∈ Algebra.adjoin k (insert θ (R : Set F)) := by
  rw [aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (g.coeff i).2))
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)

theorem exists_common_mul_mem {k F : Type} [Field k] [Field F] [Algebra k F]
    (R S : Subalgebra k F) (hRS : R ≤ S) (T : Finset F)
    (h : ∀ x ∈ T, ∃ b : R, b ≠ 0 ∧ (b : F) * x ∈ S) :
    ∃ B : R, B ≠ 0 ∧ ∀ x ∈ T, (B : F) * x ∈ S := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a T ha ih =>
    obtain ⟨B, hB, hBT⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨b, hb, hba⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨b * B, mul_ne_zero hb hB, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have : ((b * B : R) : F) * x = (B : F) * ((b : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS B.2) hba
    · have : ((b * B : R) : F) * x = (b : F) * ((B : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS b.2) (hBT x hx)

end GlobalTheory.SepPoint

namespace GlobalTheory.SepPoint

theorem exists_primitive_sep_certificate (k F : Type) [Field k] [Field F] [Algebra k F]
    (s : Finset F) (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F) (T : Finset F) :
    ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧
      ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧
        ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)),
          U * minpoly (Algebra.adjoin k (s : Set F)) θ +
              V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) =
            Polynomial.C H ∧
          ∀ x ∈ T, (H : F) * x ∈
            Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  classical
  haveI hIC := isIntegrallyClosed_adjoin k F s hs.1
  have hr : Set.range ((↑) : s → F) = (s : Set F) := Subtype.range_coe
  have halg : Algebra.IsAlgebraic (Algebra.adjoin k (s : Set F)) F := by
    have := hs.isAlgebraic
    rw [hr] at this
    exact this

  let E := IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) (T : Set F)
  haveI : FiniteDimensional (IntermediateField.adjoin k (s : Set F)) E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral _ x
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) E :=
    Algebra.isSeparable_tower_bot_of_isSeparable _ E F
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (IntermediateField.adjoin k (s : Set F)) E
  have hE : E = IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {(α : F)} := by
    rw [← IntermediateField.lift_adjoin_simple, hα, IntermediateField.lift_top]

  obtain ⟨c, hc, hcint⟩ := IsAlgebraic.exists_integral_multiple (halg.isAlgebraic (α : F))
  set θ : F := c • (α : F) with hθdef
  refine ⟨θ, hcint, ?_⟩

  have hmin : minpoly (IntermediateField.adjoin k (s : Set F)) θ =
      (minpoly (Algebra.adjoin k (s : Set F)) θ).map
        (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F))) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' _ hcint
  have hsepθ : (minpoly (IntermediateField.adjoin k (s : Set F)) θ).Separable :=
    Algebra.IsSeparable.isSeparable _ θ
  obtain ⟨u, v, huv⟩ := hsepθ
  obtain ⟨u', b₁, hb₁, hu'⟩ := exists_clear_poly (k := k) (s : Set F) u
  obtain ⟨v', b₂, hb₂, hv'⟩ := exists_clear_poly (k := k) (s : Set F) v

  have hden : ∀ x ∈ T, ∃ b : Algebra.adjoin k (s : Set F), b ≠ 0 ∧ (b : F) * x ∈
      Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
    intro x hx
    have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ hx
    rw [hE] at hxE
    have hcF : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
    have hcmem : (c : F) ∈ IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ} :=
      IntermediateField.algebraMap_mem _
        (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F)) c)
    have hαmem : (α : F) ∈ IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ} := by
      have : (α : F) = (c : F)⁻¹ * θ := by
        show (α : F) = (c : F)⁻¹ * ((c : F) * (α : F))
        rw [← mul_assoc, inv_mul_cancel₀ hcF, one_mul]
      rw [this]
      exact mul_mem (inv_mem hcmem) (IntermediateField.mem_adjoin_simple_self _ _)
    have hxθ := IntermediateField.adjoin_simple_le_iff.mpr hαmem hxE
    have hθint : IsIntegral (IntermediateField.adjoin k (s : Set F)) θ :=
      Algebra.IsSeparable.isIntegral _ θ
    have hxθ' : x ∈ (IntermediateField.adjoin (IntermediateField.adjoin k (s : Set F)) {θ}).toSubalgebra :=
      hxθ
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hxθ'
    obtain ⟨g, hg⟩ := hxθ'
    obtain ⟨q, b, hb, hq⟩ := exists_clear_poly (k := k) (s : Set F) g
    refine ⟨b, hb, ?_⟩
    have : (b : F) * x = aeval θ q := by
      rw [← hg, ← Polynomial.aeval_map_algebraMap (IntermediateField.adjoin k (s : Set F)) θ q, hq,
        Polynomial.aeval_mul, Polynomial.aeval_C]
      rfl
    rw [this]
    exact aeval_mem_adjoin_insert _ θ q
  obtain ⟨B, hB, hBT⟩ := exists_common_mul_mem (Algebra.adjoin k (s : Set F))
    (Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)))
    (fun y hy => Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)) T hden
  refine ⟨b₁ * b₂ * B, mul_ne_zero (mul_ne_zero hb₁ hb₂) hB, C (b₂ * B) * u', C (b₁ * B) * v', ?_, ?_⟩
  · apply Polynomial.map_injective
      (algebraMap (Algebra.adjoin k (s : Set F)) (IntermediateField.adjoin k (s : Set F)))
      (IsFractionRing.injective _ _)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ← Polynomial.derivative_map,
      ← hmin, hu', hv', map_mul]
    linear_combination (C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) b₁) *
      C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) b₂) *
      C (algebraMap _ (IntermediateField.adjoin k (s : Set F)) B)) * huv
  · intro x hx
    have : ((b₁ * b₂ * B : Algebra.adjoin k (s : Set F)) : F) * x =
        ((b₁ * b₂ : Algebra.adjoin k (s : Set F)) : F) * ((B : F) * x) := by push_cast; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (b₁ * b₂).2))
      (hBT x hx)

end GlobalTheory.SepPoint
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_element_separability_certificate : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F), IsTranscendenceBasis k ((↑) : s → F) → Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F → ∀ T : Finset F, ∃ θ : F, IsIntegral (Algebra.adjoin k (s : Set F)) θ ∧ ∃ H : Algebra.adjoin k (s : Set F), H ≠ 0 ∧ ∃ U V : Polynomial (Algebra.adjoin k (s : Set F)), U * minpoly (Algebra.adjoin k (s : Set F)) θ + V * Polynomial.derivative (minpoly (Algebra.adjoin k (s : Set F)) θ) = Polynomial.C H ∧ ∀ x ∈ T, (H : F) * x ∈ Algebra.adjoin k (insert θ (Algebra.adjoin k (s : Set F) : Set F)) := by
  atlas_forward_decl GlobalTheory.SepPoint.exists_primitive_sep_certificate
end

section
section
open scoped TensorProduct

namespace GlobalTheory.SepPoint

theorem exists_sepBasis (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B]
    (hB : Algebra.FiniteType k B)
    (hH : ∀ p : ℕ, p.Prime → CharP k p → ∀ s : Finset (FractionRing B),
      LinearIndepOn k _root_.id (s : Set (FractionRing B)) →
        LinearIndepOn k (· ^ p) (s : Set (FractionRing B))) :
    ∃ s : Finset (FractionRing B), IsTranscendenceBasis k ((↑) : s → FractionRing B) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set (FractionRing B)))
        (FractionRing B) := by
  haveI : Algebra.EssFiniteType k B := inferInstance
  haveI : Algebra.EssFiniteType B (FractionRing B) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors B)
  haveI : Algebra.EssFiniteType k (FractionRing B) := Algebra.EssFiniteType.comp k B _
  obtain _ | ⟨p, hp, hpk⟩ := CharP.exists' k
  · exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k _
  · haveI : ExpChar k p := .prime hp.out
    exact exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p hp.out (hH p hp.out hpk)

theorem core (k F : Type) [Field k] [Field F] [Algebra k F] (s : Finset F)
    (hs : IsTranscendenceBasis k ((↑) : s → F))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set F)) F)
    (B : Subalgebra k F) (hB : B.FG) : Nonempty (B →ₐ[k] SeparableClosure k) := by
  obtain ⟨T, rfl⟩ := hB
  haveI : IsIntegrallyClosed (Algebra.adjoin k (s : Set F)) := isIntegrallyClosed_adjoin k F s hs.1
  obtain ⟨θ, hθ, H, hH0, U, V, hUV, hT⟩ := GlobalTheory.T.exists_primitive_element_separability_certificate k F s hs hsep T
  obtain ⟨ev, hev⟩ := exists_ev k F s hs.1 H hH0
  let R := Algebra.adjoin k (s : Set F)
  let f := minpoly R θ
  let e : R →+* SeparableClosure k := (ev : R →+* SeparableClosure k)
  have hmon : f.Monic := minpoly.monic hθ
  have hsepa : (f.map e).Separable := by
    have h1 := congrArg (Polynomial.map e) hUV
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h1
    refine ⟨Polynomial.C (e H)⁻¹ * U.map e, Polynomial.C (e H)⁻¹ * V.map e, ?_⟩
    rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul,
      inv_mul_cancel₀ (show e H ≠ 0 from hev), Polynomial.C_1]
  have hdeg : (f.map e).degree ≠ 0 := by
    rw [hmon.degree_map]
    exact (minpoly.degree_pos hθ).ne'
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root _ hdeg hsepa
  have hr' : Polynomial.eval₂ (ev : R →+* SeparableClosure k) r f = 0 := by
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hr
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_algHom_adjoin_extend_of_isIntegral_root k F (SeparableClosure k) R θ hθ ev r hr'
  have hHS : (H : F) ∈ Algebra.adjoin k (insert θ (R : Set F)) :=
    Algebra.subset_adjoin (Set.mem_insert_of_mem _ H.2)
  exact GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero k F (SeparableClosure k) _ ψ ⟨H, hHS⟩
    (by rw [hψ _ H.2 hHS]; exact hev) (T : Set F) hT

theorem exists_sepPoint : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B],
    Algebra.FiniteType k B →
    (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K →
      IsDomain (K ⊗[k] B)) →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧
      Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  intro k B _ _ _ hB hK
  haveI : IsDomain (k ⊗[k] B) := hK k inferInstance inferInstance
  haveI : IsDomain B := (Algebra.TensorProduct.lid k B).symm.toMulEquiv.isDomain
  obtain ⟨s, hs, hsep⟩ := exists_sepBasis k B hB
    (fun p hp hpk => GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep k B p hp hpk hK)
  let g : B →ₐ[k] FractionRing B := IsScalarTower.toAlgHom k B (FractionRing B)
  have hfg : g.range.FG := by
    rw [← Algebra.map_top]
    exact hB.out.map g
  obtain ⟨ψ⟩ := core k (FractionRing B) s hs hsep g.range hfg
  exact GlobalTheory.T.exists_finite_separable_point_of_separableClosure_point' k B hB ⟨ψ.comp g.rangeRestrict⟩

end GlobalTheory.SepPoint
end

open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_point_of_geometrically_domain : ∀ (k B : Type) [Field k] [CommRing B] [Algebra k B], Algebra.FiniteType k B → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ Nonempty (B →ₐ[k] k') := by
  atlas_forward_decl GlobalTheory.SepPoint.exists_sepPoint
end
