import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjoinEqTopAndIsReducedOfCharpolySeparable

section
section
open GlobalTheory.UnitLemma Polynomial Module

namespace GlobalTheory.IntClosureSep

theorem isRoot_minpoly_of_isRoot_charpoly {E A L : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] [Field L] [Algebra E L] (g : A) {α : L}
    (hα : ((LinearMap.mulLeft E g).charpoly.map (algebraMap E L)).IsRoot α) :
    ((minpoly E g).map (algebraMap E L)).IsRoot α := by
  classical
  let b := Module.finBasis E A
  set M := Algebra.leftMulMatrix b g with hM
  have hQ : (LinearMap.mulLeft E g).charpoly = M.charpoly := by
    rw [← LinearMap.charpoly_toMatrix (LinearMap.mulLeft E g) b]; rfl
  set M' := M.map (algebraMap E L) with hM'
  have h1 : Module.End.HasEigenvalue (Matrix.toLin' M') α := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', Matrix.charpoly_map,
      ← hQ]
    exact hα
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  have h2 : aeval M (minpoly E g) = 0 := by
    rw [hM, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have h3 : aeval M' ((minpoly E g).map (algebraMap E L)) = 0 := by
    rw [aeval_map_algebraMap]
    have : M' = (Algebra.ofId E L).mapMatrix M := rfl
    rw [this, Polynomial.aeval_algHom_apply, h2, map_zero]
  have h4 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly E g).map (algebraMap E L)) hv
  have h5 : aeval (Matrix.toLin' M') ((minpoly E g).map (algebraMap E L)) = 0 := by
    have : Matrix.toLin' M' = Matrix.toLinAlgEquiv' M' := rfl
    rw [this, Polynomial.aeval_algEquiv, AlgHom.comp_apply, h3, map_zero]
  rw [h5, LinearMap.zero_apply] at h4
  exact (smul_eq_zero.mp h4.symm).resolve_right hv.2

theorem integralClosure_fg_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ g hsep
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (Subalgebra.toSubmodule (integralClosure O A)) ⊥]
    exact Submodule.fg_bot
  let L := AlgebraicClosure E
  set Q := (LinearMap.mulLeft E g).charpoly with hQ
  set n := finrank E A with hn
  have hQdeg : Q.natDegree = n := LinearMap.charpoly_natDegree _
  set R := (Q.map (algebraMap E L)).roots with hR
  have hRnodup : R.Nodup := nodup_roots (hsep.map)
  have hRcard : Multiset.card R = n := by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hQdeg]
  set m := minpoly E g with hm
  have hsub : ∀ α ∈ R, aeval α m = 0 := fun α hα => by
    have := isRoot_minpoly_of_isRoot_charpoly g (isRoot_of_mem_roots hα)
    rwa [IsRoot, eval_map_algebraMap] at this
  have hm_ne : m ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral g)
  have hdeg_ge : n ≤ m.natDegree := by
    have hle : R ≤ (m.map (algebraMap E L)).roots := (Multiset.le_iff_subset hRnodup).mpr
      fun α hα => by
        rw [mem_roots (Polynomial.map_ne_zero hm_ne), IsRoot, eval_map_algebraMap]
        exact hsub α hα
    calc n = Multiset.card R := hRcard.symm
      _ ≤ _ := Multiset.card_le_card hle
      _ ≤ (m.map (algebraMap E L)).natDegree := card_roots' _
      _ = m.natDegree := natDegree_map _
  have hdeg_le : m.natDegree ≤ n := by
    simpa using (linearIndependent_pow (K := E) g).fintype_card_le_finrank
  have hdeg : m.natDegree = n := le_antisymm hdeg_le hdeg_ge
  haveI : Nonempty (Fin m.natDegree) := ⟨⟨0, by rw [hdeg, hn]; exact Module.finrank_pos⟩⟩
  let pb : PowerBasis E A :=
    { gen := g, dim := m.natDegree
      basis := basisOfLinearIndependentOfCardEqFinrank (linearIndependent_pow g) (by simp [hdeg, m, n])
      basis_eq_pow := fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank] }
  let ι : Type := ↥R.toFinset
  have hcard : Fintype.card ι = n := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup hRnodup, hRcard]
  let P : ι → (A →ₐ[E] L) := fun α => pb.lift α.1 (hsub α.1 (Multiset.mem_toFinset.mp α.2))
  have hP : Function.Injective P := fun a b h => Subtype.ext (by
    have h' : (P a) pb.gen = (P b) pb.gen := congrArg (fun f : A →ₐ[E] L => f pb.gen) h
    simpa only [P, PowerBasis.lift_gen] using h')
  let b0 : Basis ι E A := (Module.finBasisOfFinrankEq E A hcard.symm).reindex (Fintype.equivFin ι).symm
  have hex : ∀ i, ∃ c : nonZeroDivisors O, IsIntegral O ((c : O) • b0 i) := fun i =>
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors O) (b0 i)
      (Algebra.IsIntegral.isIntegral (R := E) (b0 i))
  choose c hc using hex
  let e : Basis ι E A := b0.isUnitSMul (w := fun i => algebraMap O E (c i))
    (fun i => (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (c i).2).isUnit)
  have he : ∀ i, e i = (c i : O) • b0 i := fun i => by
    simp [e, Basis.isUnitSMul_apply, algebraMap_smul]
  have he_int : ∀ i, IsIntegral O (e i) := fun i => (he i) ▸ hc i
  have hdisc : Algebra.discr E e ≠ 0 := fun h =>
    GlobalTheory.algebraMap_discr_basis_ne_zero e hP (by rw [h, map_zero])
  have hnd : (Algebra.traceForm E A).Nondegenerate := by
    have hT : LinearMap.BilinForm.toMatrix e (Algebra.traceForm E A) = Algebra.traceMatrix E e := by
      ext i j
      rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero e, hT]
    exact hdisc
  have htr : ∀ x : A, IsIntegral O x → ∃ r : O, algebraMap O E r = Algebra.trace E A x := by
    intro x hx
    have h1 : IsIntegral O (algebraMap E L (Algebra.trace E A x)) := by
      rw [GlobalTheory.algebraMap_trace_eq_sum_algHom_of_card hcard hP x]
      refine IsIntegral.sum _ fun j _ => ?_
      exact hx.map ((P j).restrictScalars O)
    have h2 : IsIntegral O (Algebra.trace E A x) :=
      (isIntegral_algHom_iff ((Algebra.ofId E L).restrictScalars O)
        (algebraMap E L).injective).mp h1
    exact IsIntegrallyClosed.isIntegral_iff.mp h2
  set d := (Algebra.traceForm E A).dualBasis hnd e
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ Submodule.span O (Set.range d) := by
    intro x hx
    have hx' : IsIntegral O x := hx
    rw [← d.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    obtain ⟨r, hr⟩ := htr _ (hx'.mul (he_int i))
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.FG.of_le (Submodule.fg_span (Set.finite_range d)) hle

end GlobalTheory.IntClosureSep
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  atlas_forward_decl GlobalTheory.IntClosureSep.integralClosure_fg_of_separable_charpoly
end

section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ N : Submodule O A, IsLat O E N → (∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N) → ∃ t : Aˣ, N = mulLat O (t : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  first | exact @GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | exact GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable | (intros; apply GlobalTheory.UnitLemma.PrincipalLatDVR.eq_mulLat_integralClosure_of_separable <;> assumption)
end

section
section
open Polynomial

namespace GlobalTheory.SepGenElt

theorem exists_aeval_eq : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A),
    (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  intro E A _ _ _ _ g hs x
  have hx : x ∈ Algebra.adjoin E ({g} : Set A) := by
    rw [GlobalTheory.SepGen.adjoin_eq_top g hs]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  exact hx

end GlobalTheory.SepGenElt
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → ∀ x : A, ∃ p : E[X], aeval g p = x := by
  atlas_forward_decl GlobalTheory.SepGenElt.exists_aeval_eq
end

section
section
open Polynomial

namespace GlobalTheory

theorem exists_denominator_aeval_elem (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E]
    [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A)
    (h : ∀ x : A, ∃ p : E[X], aeval g p = x) (x : A) :
    ∃ c : O, c ≠ 0 ∧ ∃ p : O[X], aeval g p = c • x := by
  obtain ⟨q, rfl⟩ := h x
  obtain ⟨b, hb, hq⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, IsLocalization.integerNormalization (nonZeroDivisors O) q, ?_⟩
  rw [← aeval_map_algebraMap E, hq, ← algebraMap_smul E b q, map_smul, algebraMap_smul]

theorem exists_common_denominator_aeval_of_fg (O E A : Type) [CommRing O] [IsDomain O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] (g : A) (h : ∀ x : A, ∃ p : E[X], aeval g p = x)
    (S : Submodule O A) (hS : S.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  classical
  obtain ⟨s, rfl⟩ := hS
  have key : ∃ c : O, c ≠ 0 ∧ ∀ x ∈ s, ∃ p : O[X], aeval g p = c • x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_ne_zero, by simp⟩
    | insert a s _ ih =>
      obtain ⟨c, hc, hs⟩ := ih
      obtain ⟨d, hd, p, hp⟩ := exists_denominator_aeval_elem O E A g h a
      refine ⟨c * d, mul_ne_zero hc hd, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ⟨c • p, by rw [map_smul, hp, mul_smul]⟩
      · obtain ⟨q, hq⟩ := hs x hx
        exact ⟨d • q, by rw [map_smul, hq, mul_comm, mul_smul]⟩
  obtain ⟨c, hc, hs⟩ := key
  refine ⟨c, hc, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [map_add, hp, hq, smul_add]⟩
  | smul a x _ hx =>
    obtain ⟨p, hp⟩ := hx
    exact ⟨a • p, by rw [map_smul, hp, smul_comm]⟩

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_aeval_of_fg' : ∀ (O E A : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] (g : A), (∀ x : A, ∃ p : E[X], aeval g p = x) → ∀ S : Submodule O A, S.FG → ∃ c : O, c ≠ 0 ∧ ∀ x ∈ S, ∃ p : O[X], aeval g p = c • x := by
  atlas_forward_decl GlobalTheory.exists_common_denominator_aeval_of_fg
end

section
section
open Polynomial

namespace GlobalTheory

theorem finite_quot_span_singleton_of_dvr_sandwich (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [hF : Finite (IsLocalRing.ResidueField O)] (c : O) (hc : c ≠ 0) :
    Finite (O ⧸ Ideal.span {c}) := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {c} ≠ ⊥ := by simpa using hc
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hp
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  rw [hn, ← Ideal.span_singleton_pow, ← hm]
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := hF
  exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n

theorem finite_submodules_between_smul_and_self :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  intro O A _ _ _ _ _ _ C hC c hc
  haveI := finite_quot_span_singleton_of_dvr_sandwich O c hc
  haveI : Module.Finite O C := Module.Finite.iff_fg.mpr hC
  let K : Submodule O C := (Ideal.span {c}) • (⊤ : Submodule O C)
  haveI : Finite (C ⧸ K) := Submodule.finite_quotient_smul (Ideal.span {c}) Module.Finite.fg_top
  let f : Submodule O A → Set (C ⧸ K) := fun N => K.mkQ '' {x : C | (x : A) ∈ N}
  have key : ∀ N M : Submodule O A, (N ≤ C ∧ ∀ x ∈ C, c • x ∈ N) → (M ≤ C ∧ ∀ x ∈ C, c • x ∈ M) →
      f N = f M → N ≤ M := by
    intro N M hN hM h x hx
    have h1 : K.mkQ ⟨x, hN.1 hx⟩ ∈ f M := h ▸ ⟨⟨x, hN.1 hx⟩, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h1
    have h2 : y - ⟨x, hN.1 hx⟩ ∈ K := (Submodule.Quotient.eq K).mp hxy
    have h3 : ∀ z ∈ K, (z : A) ∈ M := by
      intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [Submodule.coe_smul, mul_smul]
        exact M.smul_mem a (hM.2 n n.2)
      · intro a b ha hb
        exact M.add_mem ha hb
    have h4 := M.sub_mem hy (h3 _ h2)
    simpa using h4
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro N hN M hM h
  exact le_antisymm (key N M hN hM h) (key M N hM hN h.symm)

end GlobalTheory
end

open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [AddCommGroup A] [Module O A] (C : Submodule O A), C.FG → ∀ c : O, c ≠ 0 → {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}.Finite := by
  atlas_forward_decl GlobalTheory.finite_submodules_between_smul_and_self
end

section
section
open Polynomial

namespace GlobalTheory.UnitLemma

theorem aeval_mul_mem_of_stable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {g : A} {M : Submodule O A}
    (hM : ∀ y ∈ M, g * y ∈ M) (p : O[X]) {m : A} (hm : m ∈ M) : aeval g p * m ∈ M := by
  induction p using Polynomial.induction_on with
  | C a => simpa [Algebra.smul_def] using M.smul_mem a hm
  | add p q hp hq => simpa [add_mul] using M.add_mem hp hq
  | monomial n a ih =>
    have := hM _ ih
    have e : aeval g (Polynomial.C a * X ^ (n + 1)) * m = g * (aeval g (Polynomial.C a * X ^ n) * m) := by
      simp only [map_mul, aeval_C, aeval_X, map_pow, pow_succ]; ring
    rw [e]; exact this

theorem finite_orbits_stLat_of_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  intro O E A _ _ _ _ _ _ _ _ _ _ _ _ g hsep
  set C : Submodule O A := Subalgebra.toSubmodule (integralClosure O A) with hCdef
  have hCfg : C.FG := GlobalTheory.T.integralClosure_fg_dvr_of_separable_charpoly O E A g hsep
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_common_denominator_aeval_of_fg' O E A g (GlobalTheory.T.exists_aeval_eq_of_mulLeft_charpoly_separable E A g hsep) C hCfg
  have hfin := GlobalTheory.T.finite_setOf_submodule_between_smul_and_fg O A C hCfg c hc0

  have key : ∀ M : stLat O E g, ∃ t : Aˣ, mulLat O ((t⁻¹ : Aˣ) : A) (M : Submodule O A) ∈
      {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N} := by
    intro M
    obtain ⟨hML, hMg⟩ := M.2
    set N : Submodule O A := C * (M : Submodule O A) with hN
    have hMN : (M : Submodule O A) ≤ N := by
      intro m hm
      have := Submodule.mul_mem_mul (show (1 : A) ∈ C from (integralClosure O A).one_mem) hm
      simpa using this
    have hNlat : IsLat O E N := by
      refine ⟨Submodule.FG.mul hCfg hML.1, ?_⟩
      rw [eq_top_iff, ← hML.2]
      exact Submodule.span_mono hMN
    have hNC : ∀ x ∈ integralClosure O A, ∀ y ∈ N, x * y ∈ N := by
      intro x hx y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        rw [← mul_assoc]
        exact Submodule.mul_mem_mul ((integralClosure O A).mul_mem hx ha) hm
      · intro u v hu hv
        rw [mul_add]; exact N.add_mem hu hv
    obtain ⟨t, ht⟩ := GlobalTheory.T.eq_submoduleMulLeftImage_integralClosure_of_separable O E A g hsep N hNlat hNC
    have hcN : ∀ y ∈ N, c • y ∈ (M : Submodule O A) := by
      intro y hy
      refine Submodule.mul_induction_on hy ?_ ?_
      · intro a ha m hm
        obtain ⟨p, hp⟩ := hc a ha
        rw [← smul_mul_assoc, ← hp]
        exact aeval_mul_mem_of_stable hMg p hm
      · intro u v hu hv
        rw [smul_add]; exact Submodule.add_mem _ hu hv
    refine ⟨t, ?_, ?_⟩
    · intro x hx
      rw [mem_mulLat_iff, inv_inv] at hx
      have h1 : (t : A) * x ∈ N := hMN hx
      rw [ht, mem_mulLat_iff] at h1
      rw [hCdef, Subalgebra.mem_toSubmodule]
      rw [Subalgebra.mem_toSubmodule] at h1
      simpa [← mul_assoc] using h1
    · intro y hy
      rw [mem_mulLat_iff, inv_inv]
      have h1 : (t : A) * y ∈ N := by
        rw [ht, mem_mulLat_iff, Subalgebra.mem_toSubmodule]
        rw [hCdef, Subalgebra.mem_toSubmodule] at hy
        simpa [← mul_assoc] using hy
      simpa [mul_smul_comm] using hcN _ h1
  choose t ht using key
  let F : MulAction.orbitRel.Quotient Aˣ (stLat O E g) → {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} :=
    fun q => ⟨_, ht q.out⟩
  haveI : Finite {N : Submodule O A // N ∈ {N : Submodule O A | N ≤ C ∧ ∀ x ∈ C, c • x ∈ N}} := hfin.to_subtype
  refine Finite.of_injective F ?_
  intro q₁ q₂ h
  have h' : mulLat O (((t q₁.out)⁻¹ : Aˣ) : A) (q₁.out : Submodule O A) = mulLat O (((t q₂.out)⁻¹ : Aˣ) : A) (q₂.out : Submodule O A) :=
    congrArg Subtype.val h
  rw [← q₁.out_eq, ← q₂.out_eq]
  apply Quotient.sound
  refine ⟨t q₁.out * (t q₂.out)⁻¹, ?_⟩
  apply Subtype.ext
  rw [stLat_smul_val, Units.val_mul, mulLat_mul, ← h', ← mulLat_mul]
  simp [mulLat_one]

end GlobalTheory.UnitLemma
end

open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_unit_orbits_stable_lattices_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  atlas_forward_decl GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable
end
