import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationFormIntPolynomialBundlesStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmpleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SumMonomialAddSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsDimSymmetricAmplePowEqMulPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateBasisMatrix
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphism

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A), IsMonHom α → IsFinite α.left → Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1} ∧ ∃ e : ℕ, MapDeg α.left (ringExpChar K ^ e * Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ α = 1}) := by
  first | exact @GlobalTheory.mapDeg_eq_pow_mul_card_ker | exact GlobalTheory.mapDeg_eq_pow_mul_card_ker | (intros; apply GlobalTheory.mapDeg_eq_pow_mul_card_ker <;> assumption)
end

section
namespace GlobalTheory.NormDetIndex

open Module Submodule

theorem norm_card_quotient_span (l : ℕ) [Fact (Nat.Prime l)] {x : ℤ_[l]} (hx : x ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) : ℕ) : ℚ_[l])‖ = ‖x‖ := by
  have h1 : Ideal.span ({x} : Set ℤ_[l]) = RingHom.ker (PadicInt.toZModPow (p := l) x.valuation) := by
    rw [PadicInt.ker_toZModPow, Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hx, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hx).symm
  have h2 : Function.Surjective (PadicInt.toZModPow (p := l) x.valuation) :=
    ZMod.ringHom_surjective _
  rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective h2).toEquiv, Nat.card_zmod,
    PadicInt.norm_eq_zpow_neg_valuation hx, Nat.cast_pow, Padic.norm_p_pow]

theorem norm_eq_of_associated (l : ℕ) [Fact (Nat.Prime l)] {x y : ℤ_[l]} (h : Associated x y) :
    ‖x‖ = ‖y‖ := by
  obtain ⟨u, rfl⟩ := h
  rw [norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]

theorem norm_det_eq_norm_index (l : ℕ) [Fact (Nat.Prime l)] {κ : Type} [Fintype κ]
    [DecidableEq κ] (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℚ_[l])‖ := by
  set N := LinearMap.range M.mulVecLin with hN
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hv
  let e : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := LinearEquiv.ofInjective _ hinj
  let b : Basis κ ℤ_[l] (κ → ℤ_[l]) := Pi.basisFun _ _
  have h : finrank ℤ_[l] N = finrank ℤ_[l] (κ → ℤ_[l]) := e.symm.finrank_eq
  let a := smithNormalFormCoeffs b h
  let b' := smithNormalFormTopBasis b h
  let ab := smithNormalFormBotBasis b h
  let e' : (κ → ℤ_[l]) ≃ₗ[ℤ_[l]] N := b'.equiv ab (Equiv.refl _)
  have h1 : M.det = LinearMap.det (N.subtype ∘ₗ (e : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) := by
    rw [← LinearMap.det_toLin' M]
    rfl
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    have ha : (N.subtype ∘ₗ (e' : (κ → ℤ_[l]) →ₗ[ℤ_[l]] N)) (b' j) = a j • b' j := by
      change ((b'.equiv ab (Equiv.refl _) (b' j) : N) : κ → ℤ_[l]) = _
      rw [b'.equiv_apply, Equiv.refl_apply]
      exact smithNormalFormBotBasis_def b h j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have h3 : N.toAddSubgroup.index
      = ∏ i, Nat.card (ℤ_[l] ⧸ Ideal.span ({a i} : Set ℤ_[l])) := by
    change Nat.card ((κ → ℤ_[l]) ⧸ N) = _
    rw [Nat.card_congr (quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  rw [h1, norm_eq_of_associated l (LinearMap.associated_det_comp_equiv N.subtype e e'), h2, h3,
    Nat.cast_prod, norm_prod, norm_prod]
  exact Finset.prod_congr rfl fun i _ =>
    (norm_card_quotient_span l (smithNormalFormCoeffs_ne_zero b h i)).symm

end GlobalTheory.NormDetIndex
end

section
section
namespace GlobalTheory
namespace TorsionMatrix

section
open Matrix

theorem norm_card_quot_span (l : ℕ) [Fact l.Prime] {a : ℤ_[l]} (ha : a ≠ 0) :
    ‖((Nat.card (ℤ_[l] ⧸ Ideal.span {a}) : ℕ) : ℚ_[l])‖ = ‖a‖ := by
  have h1 : Ideal.span {a} = RingHom.ker (PadicInt.toZModPow (p := l) a.valuation) := by
    rw [PadicInt.ker_toZModPow]
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have h2 : Nat.card (ℤ_[l] ⧸ Ideal.span {a}) = l ^ a.valuation := by
    rw [h1, Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := l) a.valuation))).toEquiv, Nat.card_zmod]
  rw [h2, PadicInt.norm_eq_zpow_neg_valuation ha]
  push_cast
  rw [Padic.norm_p_pow]

theorem norm_index_range (l : ℕ) [Fact l.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : Matrix κ κ ℤ_[l]) (hM : M.det ≠ 0) :
    ‖M.det‖ = ‖(((LinearMap.range M.mulVecLin).toAddSubgroup.index : ℕ) : ℚ_[l])‖ := by
  first
  | exact @_root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index
  | exact _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index
  | (apply _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormDetIndex.norm_det_eq_norm_index ..)

theorem norm_card_eq_torsion (l : ℕ) [hl : Fact l.Prime] (K : Type) [AddCommGroup K] [Finite K]
    (N : ℕ) (hN : Nat.card K ≤ N) :
    ‖((Nat.card K : ℕ) : ℚ_[l])‖ = ‖((Nat.card {x : K // l ^ N • x = 0} : ℕ) : ℚ_[l])‖ := by
  let T : AddSubgroup K := (nsmulAddMonoidHom (α := K) (l ^ N)).ker
  have hT : ∀ x, x ∈ T ↔ l ^ N • x = 0 := fun x => Iff.rfl
  have h1 : Nat.card K = Nat.card (K ⧸ T) * Nat.card {x : K // l ^ N • x = 0} :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T
  have h2 : ¬ l ∣ Nat.card (K ⧸ T) := by
    intro hd
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' l hd
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h3 : l • x ∈ T := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul,
        ← addOrderOf_dvd_iff_nsmul_eq_zero, hy]
    rw [hT, smul_smul, ← pow_succ, ← addOrderOf_dvd_iff_nsmul_eq_zero,
      Nat.dvd_prime_pow hl.out] at h3
    obtain ⟨k, -, hk⟩ := h3
    have h4 : k ≤ N := by
      have := addOrderOf_le_card (x := x)
      have := Nat.lt_pow_self (n := k) hl.out.one_lt
      omega
    have h5 : x ∈ T := by
      rw [hT, ← addOrderOf_dvd_iff_nsmul_eq_zero, hk]
      exact pow_dvd_pow _ h4
    rw [(QuotientAddGroup.eq_zero_iff x).2 h5, addOrderOf_zero] at hy
    exact hl.out.one_lt.ne hy
  rw [h1, Nat.cast_mul, norm_mul, Padic.norm_natCast_eq_one_iff.2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 h2), one_mul]

theorem exists_zmod_basis (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (V : Type) [AddCommGroup V]
    [Module (ZMod l) V] (hc1 : Nat.card V = l ^ m) :
    ∃ b : Fin m → V, ∀ x : V, ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • b j := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hc1]; exact pow_ne_zero _ hl.out.ne_zero)
  have hr : Module.finrank (ZMod l) V = m := by
    have := Module.natCard_eq_pow_finrank (K := ZMod l) (V := V)
    rw [hc1, Nat.card_zmod] at this
    exact (Nat.pow_right_injective hl.out.two_le this).symm
  let b := Module.finBasisOfFinrankEq (ZMod l) V hr
  have hs : ∀ t : Fin m → ZMod l, ∑ j, (t j).val • b j = b.equivFun.symm t := by
    intro t
    rw [b.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul (ZMod l), ZMod.natCast_zmod_val]
  refine ⟨b, fun x => ⟨b.equivFun x, ?_, fun t ht => ?_⟩⟩
  · simp only [hs, LinearEquiv.symm_apply_apply]
  · simp only [hs] at ht
    rw [ht, LinearEquiv.apply_symm_apply]

theorem exists_tower (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q]
    (h : ∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) :
    ∃ τ : Fin m → ℕ → Q, (∀ i n, (l ^ (n + 1)) • τ i n = 0) ∧ (∀ i n, τ i n = l • τ i (n + 1)) ∧
      (∀ x : Q, l • x = 0 → ∃! t : Fin m → ZMod l, x = ∑ j, (t j).val • τ j 0) := by
  let T : ℕ → AddSubgroup Q := fun k => (nsmulAddMonoidHom (α := Q) k).ker
  have hT : ∀ k x, x ∈ T k ↔ k • x = 0 := fun k x => Iff.rfl
  have hc : ∀ j, Nat.card (T (l ^ j)) = l ^ (m * j) := h
  have hc1 : Nat.card (T l) = l ^ m := by simpa using hc 1
  have hfin : ∀ j, Finite (T (l ^ j)) := fun j =>
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.out.ne_zero)
  have hsurj : ∀ j (x : Q), l ^ j • x = 0 → ∃ y : Q, l ^ (j + 1) • y = 0 ∧ x = l • y := by
    intro j x hx
    have := hfin j
    have := hfin (j + 1)
    let φ : T (l ^ (j + 1)) →+ T (l ^ j) :=
      ((nsmulAddMonoidHom (α := Q) l).comp (T (l ^ (j + 1))).subtype).codRestrict _ fun y => by
        have := (hT _ _).1 y.2
        change l ^ j • l • (y : Q) = 0
        rw [smul_smul, ← pow_succ]
        exact this
    have hφ : ∀ y, (φ y : Q) = l • (y : Q) := fun y => rfl
    have hk : Nat.card φ.ker = l ^ m := by
      rw [← hc1]
      refine Nat.card_congr ⟨fun y => ⟨y.1.1, ?_⟩, fun y => ⟨⟨y.1, ?_⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
      · exact congrArg Subtype.val y.2
      · rw [hT, pow_succ, mul_smul, (hT _ _).1 y.2, smul_zero]
      · exact Subtype.ext y.2
    have h1 := AddSubgroup.card_mul_index φ.ker
    rw [AddSubgroup.index_ker, hk, hc, mul_add, mul_one, pow_add l (m * j), mul_comm] at h1
    have h2 : Nat.card φ.range = Nat.card (T (l ^ j)) := by
      rw [hc]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hl.out.pos m) h1
    have h3 : φ.range = ⊤ := AddSubgroup.eq_top_of_card_eq _ h2
    obtain ⟨y, hy⟩ := AddMonoidHom.range_eq_top.1 h3 ⟨x, hx⟩
    exact ⟨y, y.2, (congrArg Subtype.val hy).symm⟩
  choose! g hg1 hg2 using hsurj
  obtain ⟨b, hb⟩ := @exists_zmod_basis l hl m (T l) _
    (AddCommGroup.zmodModule fun x => Subtype.ext x.2) hc1
  let τ : Fin m → ℕ → Q := fun i n => Nat.rec (b i : Q) (fun k x => g (k + 1) x) n
  have h1 : ∀ i n, (l ^ (n + 1)) • τ i n = 0 := by
    intro i n
    induction n with
    | zero => rw [zero_add, pow_one]; exact (b i).2
    | succ n ih => exact hg1 _ _ ih
  have hs : ∀ t : Fin m → ZMod l,
      ((∑ j, (t j).val • b j : T l) : Q) = ∑ j, (t j).val • τ j 0 := by
    intro t
    rw [AddSubgroup.val_finset_sum]
    rfl
  refine ⟨τ, h1, fun i n => hg2 _ _ (h1 i n), fun x hx => ?_⟩
  simpa only [Subtype.ext_iff, hs] using hb ⟨x, hx⟩

theorem card_ker_eq_index (l : ℕ) [hl : Fact l.Prime] {κ : Type} [Fintype κ] [DecidableEq κ]
    (M A : Matrix κ κ ℤ_[l]) (N : ℕ) (h1 : M * A = ((l : ℤ_[l]) ^ N) • 1)
    (h2 : A * M = ((l : ℤ_[l]) ^ N) • 1) :
    Nat.card {t : κ → ZMod (l ^ N) // (M.map (PadicInt.toZModPow N)) *ᵥ t = 0} =
      (LinearMap.range M.mulVecLin).toAddSubgroup.index := by
  set π := PadicInt.toZModPow (p := l) N with hπ
  have hl0 : ((l : ℤ_[l]) ^ N) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have hz : ∀ y : κ → ℤ_[l], π ∘ y = 0 ↔ ∃ z : κ → ℤ_[l], y = ((l : ℤ_[l]) ^ N) • z := by
    intro y
    have : ∀ a : ℤ_[l], π a = 0 ↔ ∃ z, a = ((l : ℤ_[l]) ^ N) * z := by
      intro a
      rw [← RingHom.mem_ker, hπ, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; rfl
    constructor
    · intro h
      choose z hz using fun i => (this (y i)).1 (congrFun h i)
      exact ⟨z, funext hz⟩
    · rintro ⟨z, rfl⟩
      exact funext fun i => (this _).2 ⟨z i, rfl⟩
  have hc : ∀ (P R : Matrix κ κ ℤ_[l]), R * P = ((l : ℤ_[l]) ^ N) • 1 →
      ∀ y z : κ → ℤ_[l], P *ᵥ y = P *ᵥ z → y = z := by
    intro P R h y z hyz
    have := congrArg (R *ᵥ ·) hyz
    simp only [mulVec_mulVec, h, smul_mulVec, one_mulVec] at this
    exact smul_right_injective _ hl0 this
  have hmap : ∀ y : κ → ℤ_[l], (M.map π) *ᵥ (π ∘ y) = π ∘ (M *ᵥ y) := fun y =>
    funext fun i => (RingHom.map_mulVec π M y i).symm
  let φ : (κ → ℤ_[l]) →+ (κ → ZMod (l ^ N)) :=
    (π.toAddMonoidHom.compLeft κ).comp A.mulVecLin.toAddMonoidHom
  have hφ : ∀ y, φ y = π ∘ (A *ᵥ y) := fun y => rfl
  have hk : φ.ker = (LinearMap.range M.mulVecLin).toAddSubgroup := by
    ext y
    rw [AddMonoidHom.mem_ker, hφ, hz]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, hc A M h1 _ _ ?_⟩
      rw [mulVecLin_apply, mulVec_mulVec, h2, hz, smul_mulVec, one_mulVec]
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [mulVecLin_apply, mulVec_mulVec, h2, smul_mulVec, one_mulVec]⟩
  rw [← hk, AddSubgroup.index_ker]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun t => ?_)
  constructor
  · intro ht
    choose y hy using fun i => ZMod.ringHom_surjective π (t i)
    obtain rfl : π ∘ y = t := funext hy
    rw [hmap, hz] at ht
    obtain ⟨z, hz⟩ := ht
    refine ⟨z, ?_⟩
    rw [hφ, hc M A h2 (A *ᵥ z) y]
    rw [mulVec_mulVec, h1, hz, smul_mulVec, one_mulVec]
  · rintro ⟨z, rfl⟩
    rw [hφ, hmap, hz]
    exact ⟨z, by rw [mulVec_mulVec, h1, smul_mulVec, one_mulVec]⟩

section ev
variable {Q κ : Type} [AddCommGroup Q] [Fintype κ] {N : ℕ} [NeZero N]

theorem val_add_smul {x : Q} (hx : N • x = 0) (a b : ZMod N) :
    (a + b).val • x = a.val • x + b.val • x := by
  rw [ZMod.val_add, ← nsmul_eq_mod_nsmul _ hx, add_smul]

theorem val_mul_smul {x : Q} (hx : N • x = 0) (a b : ZMod N) :
    (a * b).val • x = b.val • a.val • x := by
  rw [ZMod.val_mul, ← nsmul_eq_mod_nsmul _ hx, mul_comm, mul_smul]

def ev (pt : κ → Q) (h : ∀ i, N • pt i = 0) : (κ → ZMod N) →+ Q :=
  AddMonoidHom.mk' (fun t => ∑ i, (t i).val • pt i) fun a b => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => val_add_smul (h i) _ _

theorem ev_apply (pt : κ → Q) (h : ∀ i, N • pt i = 0) (t : κ → ZMod N) :
    ev pt h t = ∑ i, (t i).val • pt i := rfl

theorem nsmul_ev (pt : κ → Q) (h : ∀ i, N • pt i = 0) (t : κ → ZMod N) : N • ev pt h t = 0 := by
  rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]

theorem map_ev (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0) (h' : ∀ i, N • pt' i = 0)
    (M : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt' i) (t : κ → ZMod N) :
    g (ev pt h t) = ev pt' h' (M *ᵥ t) := by
  have : M *ᵥ t = ∑ j, fun i => M i j * t j := by
    funext i
    simp [mulVec, dotProduct, Finset.sum_apply]
  rw [this, map_sum, ev_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_nsmul, hM, ev_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (val_mul_smul (h' i) _ _).symm

theorem ev_injective {pt : κ → Q} (h : ∀ i, N • pt i = 0)
    (hb : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt i = y) :
    Function.Injective (ev pt h) := fun a b hab =>
  (hb _ (nsmul_ev pt h b)).unique hab rfl

theorem det_eq_det [DecidableEq κ] (g : Q →+ Q) {pt pt' : κ → Q} (h : ∀ i, N • pt i = 0)
    (h' : ∀ i, N • pt' i = 0)
    (hb : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt i = y)
    (hb' : ∀ y : Q, N • y = 0 → ∃! c : κ → ZMod N, ∑ i, (c i).val • pt' i = y)
    (M M' : Matrix κ κ (ZMod N)) (hM : ∀ j, g (pt j) = ∑ i, (M i j).val • pt i)
    (hM' : ∀ j, g (pt' j) = ∑ i, (M' i j).val • pt' i) : M.det = M'.det := by
  choose P hP using fun j => (hb' _ (h j)).exists
  choose P' hP' using fun j => (hb _ (h' j)).exists
  have e1 := map_ev (AddMonoidHom.id Q) h h' (Matrix.of P)ᵀ fun j => (hP j).symm
  have e2 := map_ev (AddMonoidHom.id Q) h' h (Matrix.of P')ᵀ fun j => (hP' j).symm
  simp only [AddMonoidHom.id_apply] at e1 e2
  have f1 : (Matrix.of P)ᵀ * (Matrix.of P')ᵀ = 1 := by
    refine Matrix.mulVec_injective (funext fun t => ev_injective h' hb' ?_)
    rw [← mulVec_mulVec, ← e1, ← e2, one_mulVec]
  have f2 : (Matrix.of P)ᵀ * M = M' * (Matrix.of P)ᵀ := by
    refine Matrix.mulVec_injective (funext fun t => ev_injective h' hb' ?_)
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← e1, ← map_ev g h' h' M' hM', ← e1,
      ← map_ev g h h M hM]
  have hu := Matrix.isUnit_det_of_right_inverse f1
  have := congrArg Matrix.det f2
  rw [det_mul, det_mul, mul_comm] at this
  exact hu.mul_right_cancel this

end ev

theorem norm_det_eq (l : ℕ) [hl : Fact l.Prime] {κ Q : Type} [Fintype κ] [DecidableEq κ]
    [AddCommGroup Q] (τ : κ → ℕ → Q) (h1 : ∀ i n, (l ^ (n + 1)) • τ i n = 0)
    (hb : ∀ n (x : Q), (l ^ (n + 1)) • x = 0 →
      ∃! t : κ → ZMod (l ^ (n + 1)), ∑ j, (t j).val • τ j n = x)
    (f : Q →+ Q) (M : Matrix κ κ ℤ_[l])
    (hM : ∀ j n, f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (M k j)).val • τ k n)
    [Finite f.ker] : ‖M.det‖ = ‖((Nat.card f.ker : ℕ) : ℚ_[l])‖ := by
  have hev : ∀ n t, f (ev (fun i => τ i n) (fun i => h1 i n) t) =
      ev (fun i => τ i n) (fun i => h1 i n) ((M.map (PadicInt.toZModPow (n + 1))) *ᵥ t) :=
    fun n => map_ev f _ _ _ fun j => hM j n
  have hinj : ∀ n, Function.Injective (ev (fun i => τ i n) (fun i => h1 i n)) :=
    fun n => ev_injective _ (hb n)
  have hc0 : Nat.card f.ker ≠ 0 := Nat.card_pos.ne'
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    funext i
    have key : ∀ n, PadicInt.toZModPow (n + 1) (Nat.card f.ker • v i) = 0 := by
      intro n
      have hk : ev (fun i => τ i n) (fun i => h1 i n) (PadicInt.toZModPow (n + 1) ∘ v) ∈ f.ker := by
        rw [AddMonoidHom.mem_ker, hev]
        have : (M.map (PadicInt.toZModPow (n + 1))) *ᵥ (PadicInt.toZModPow (n + 1) ∘ v) = 0 := by
          funext k
          rw [← RingHom.map_mulVec, hv]
          simp
        rw [this, map_zero]
      have h2 := congrArg Subtype.val (card_nsmul_eq_zero' (x := (⟨_, hk⟩ : f.ker)))
      rw [AddSubgroup.coe_nsmul, ← map_nsmul, ZeroMemClass.coe_zero,
        map_eq_zero_iff _ (hinj n)] at h2
      rw [map_nsmul]
      exact congrFun h2 i
    have : Nat.card f.ker • v i = 0 := by
      rw [← PadicInt.ext_of_toZModPow]
      intro n
      rw [map_zero]
      cases n with
      | zero =>
        have : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero l)
        exact Subsingleton.elim _ _
      | succ n => exact key n
    rw [nsmul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left (Nat.cast_ne_zero.2 hc0)
  set n := M.det.valuation + Nat.card f.ker with hn
  obtain ⟨c, hc⟩ : M.det ∣ (l : ℤ_[l]) ^ (n + 1) := by
    rw [PadicInt.unitCoeff_spec hdet, Units.mul_left_dvd]
    exact pow_dvd_pow _ (by omega)
  have a1 : M * (c • M.adjugate) = ((l : ℤ_[l]) ^ (n + 1)) • 1 := by
    rw [Matrix.mul_smul, mul_adjugate, smul_smul, hc, mul_comm]
  have a2 : (c • M.adjugate) * M = ((l : ℤ_[l]) ^ (n + 1)) • 1 := by
    rw [Matrix.smul_mul, adjugate_mul, smul_smul, hc, mul_comm]
  rw [norm_index_range l M hdet, ← card_ker_eq_index l M _ _ a1 a2,
    norm_card_eq_torsion l f.ker (n + 1) (by omega)]
  congr 2
  refine Nat.card_eq_of_bijective (fun t => ⟨⟨ev (fun i => τ i n) (fun i => h1 i n) t.1, ?_⟩,
    Subtype.ext (nsmul_ev _ _ _)⟩) ⟨fun a b hab => ?_, fun x => ?_⟩
  · rw [AddMonoidHom.mem_ker, hev, t.2, map_zero]
  · exact Subtype.ext (hinj n (congrArg (fun z => z.1.1) hab))
  · obtain ⟨t, ht, -⟩ := hb n x.1.1 (congrArg Subtype.val x.2)
    refine ⟨⟨t, hinj n ?_⟩, Subtype.ext (Subtype.ext ht)⟩
    rw [← hev, ev_apply, ht, map_zero]
    exact x.1.2

end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem exists_padic_matrix : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q] (s : Module.End ℤ Q), (∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) → ∃ U : Matrix (Fin m) (Fin m) ℤ_[l], (∀ F : Polynomial ℤ, Finite {x : Q // Polynomial.aeval s F x = 0} → ‖(Polynomial.aeval U F).det‖ = ‖((Nat.card {x : Q // Polynomial.aeval s F x = 0} : ℕ) : ℚ_[l])‖) ∧ (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ∀ (j : ℕ) (x : Q), l ^ j • x = 0 → Polynomial.aeval s F x = 0) ∧ ∀ (j : ℕ) (pt : Fin m → Q) (Mat : Matrix (Fin m) (Fin m) (ZMod (l ^ j))), (∀ i, l ^ j • pt i = 0) → (∀ y : Q, l ^ j • y = 0 → ∃! c : Fin m → ZMod (l ^ j), ∑ i, (c i).val • pt i = y) → (∀ i, s (pt i) = ∑ i', (Mat i' i).val • pt i') → PadicInt.toZModPow j U.det = Mat.det := by
  intro l hl m Q _ s h
  obtain ⟨τ, h1, h2, h3⟩ := exists_tower l m Q h
  obtain ⟨hb0, ρ0, hρ0⟩ := GlobalTheory.tate_basis_matrix l (Fin m) Q τ h1 h2 h3
  have hb : ∀ n (x : Q), (l ^ (n + 1)) • x = 0 →
      ∃! t : Fin m → ZMod (l ^ (n + 1)), ∑ j, (t j).val • τ j n = x := by
    intro n x hx
    simpa only [eq_comm] using hb0 n x hx
  let ρ : Module.End ℤ Q →+* Matrix (Fin m) (Fin m) ℤ_[l] :=
    ρ0.comp (addMonoidEndRingEquivInt Q).symm.toRingHom
  have hρ : ∀ (f : Module.End ℤ Q) j n,
      f (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (ρ f k j)).val • τ k n :=
    fun f j n => hρ0 ((addMonoidEndRingEquivInt Q).symm f) j n
  have hF : ∀ F : Polynomial ℤ, Polynomial.aeval (ρ s) F = ρ (Polynomial.aeval s F) :=
    fun F => Polynomial.aeval_algHom_apply ρ.toIntAlgHom s F
  refine ⟨ρ s, fun F hfin => ?_, fun F h0 j x hx => ?_, fun j pt Mat hpt hbp hs => ?_⟩
  · rw [hF]
    have : Finite (Polynomial.aeval s F).toAddMonoidHom.ker := hfin
    exact norm_det_eq l τ h1 hb (Polynomial.aeval s F).toAddMonoidHom _ (hρ _)
  · obtain ⟨t, ht, -⟩ := hb j x (by rw [pow_succ', mul_smul, hx, smul_zero])
    rw [← ht, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_nsmul, hρ, ← hF, h0]
    simp
  · cases j with
    | zero =>
      have : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero l)
      exact Subsingleton.elim _ _
    | succ n =>
      rw [RingHom.map_det]
      exact det_eq_det s.toAddMonoidHom (fun i => h1 i n) hpt (hb n) hbp _ _
        (fun j => hρ s j n) hs

end TorsionMatrix
end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_polynomial_det_norm_fixed_points : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (Q : Type) [AddCommGroup Q] (s : Module.End ℤ Q), (∀ j : ℕ, Nat.card {x : Q // l ^ j • x = 0} = l ^ (m * j)) → ∃ U : Matrix (Fin m) (Fin m) ℤ_[l], (∀ F : Polynomial ℤ, Finite {x : Q // Polynomial.aeval s F x = 0} → ‖(Polynomial.aeval U F).det‖ = ‖((Nat.card {x : Q // Polynomial.aeval s F x = 0} : ℕ) : ℚ_[l])‖) ∧ (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ∀ (j : ℕ) (x : Q), l ^ j • x = 0 → Polynomial.aeval s F x = 0) ∧ ∀ (j : ℕ) (pt : Fin m → Q) (Mat : Matrix (Fin m) (Fin m) (ZMod (l ^ j))), (∀ i, l ^ j • pt i = 0) → (∀ y : Q, l ^ j • y = 0 → ∃! c : Fin m → ZMod (l ^ j), ∑ i, (c i).val • pt i = y) → (∀ i, s (pt i) = ∑ i', (Mat i' i).val • pt i') → PadicInt.toZModPow j U.det = Mat.det := by
  atlas_forward_decl GlobalTheory.TorsionMatrix.exists_padic_matrix
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace ResultantNorm

open Polynomial Filter Topology

theorem exists_prod_aeval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (a : Multiset Ω)
    (P : K[X]) (hP : P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod) (F : K[X]) :
    ∃ u : K, algebraMap K Ω u = (a.map fun x => aeval x F).prod := by
  have hs : (P.map (algebraMap K Ω)).Splits := by
    rw [hP]; exact Splits.multisetProd (by
      intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
  have hm : (P.map (algebraMap K Ω)).Monic := by
    rw [hP]; exact monic_multisetProd_X_sub_C a
  have hr : (P.map (algebraMap K Ω)).roots = a := by
    rw [hP]; exact roots_multiset_prod_X_sub_C a
  refine ⟨resultant P F (P.map (algebraMap K Ω)).natDegree F.natDegree, ?_⟩
  rw [← resultant_map_map, resultant_eq_prod_eval _ _ _ natDegree_map_le hs, hm.leadingCoeff,
    one_pow, _root_.one_mul, hr]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  rw [eval_map_algebraMap]

theorem eq_of_countP {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [DecidableEq Ω] (n : ℕ) : ∀ (a b : Multiset Ω) (P Q : K[X]), a.card = n →
      P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod →
      Q.map (algebraMap K Ω) = (b.map fun x => X - C x).prod →
      (∀ G : K[X], a.countP (fun x => aeval x G = 0) = b.countP (fun x => aeval x G = 0)) →
      P = Q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b P Q hn hP hQ h
  have hinj := map_injective (algebraMap K Ω) (algebraMap K Ω).injective
  by_cases ha : a = 0
  · have h0 := h 0
    subst ha
    simp at h0
    have hb : b = 0 := by
      rw [← Multiset.card_eq_zero]
      simpa using h0.symm
    subst hb
    exact hinj (hP.trans hQ.symm)
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero ha
  have hxi : IsIntegral K x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  set G := minpoly K x with hG
  have hpos : 0 < b.countP (fun y => aeval y G = 0) := by
    rw [← h G]; exact Multiset.countP_pos.2 ⟨x, hx, minpoly.aeval K x⟩
  obtain ⟨y, hy, hyG⟩ := Multiset.countP_pos.1 hpos
  have hGy : G = minpoly K y :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hxi) hyG (minpoly.monic hxi)
  have hGm : (G.map (algebraMap K Ω)).Monic := (minpoly.monic hxi).map _
  have key : ∀ (c : Multiset Ω) (R : K[X]) (z : Ω), z ∈ c → G = minpoly K z →
      R.map (algebraMap K Ω) = (c.map fun x => X - C x).prod →
      ∃ (c' : Multiset Ω) (R' : K[X]), R = G * R' ∧ c = (G.map (algebraMap K Ω)).roots + c' ∧
        R'.map (algebraMap K Ω) = (c'.map fun x => X - C x).prod := by
    intro c R z hz hGz hR
    have hs : (R.map (algebraMap K Ω)).Splits := by
      rw [hR]; exact Splits.multisetProd (by
        intro f hf; obtain ⟨x, -, rfl⟩ := Multiset.mem_map.1 hf; exact Splits.X_sub_C x)
    have hm : (R.map (algebraMap K Ω)).Monic := by
      rw [hR]; exact monic_multisetProd_X_sub_C c
    have hr : (R.map (algebraMap K Ω)).roots = c := by
      rw [hR]; exact roots_multiset_prod_X_sub_C c
    have hz0 : aeval z R = 0 := by
      rw [← hr] at hz
      have := (mem_roots hm.ne_zero).1 hz
      rwa [IsRoot.def, eval_map_algebraMap] at this
    obtain ⟨R', hR'⟩ : G ∣ R := hGz ▸ minpoly.dvd K z hz0
    have hmul : R.map (algebraMap K Ω) = G.map (algebraMap K Ω) * R'.map (algebraMap K Ω) := by
      rw [hR', Polynomial.map_mul]
    refine ⟨(R'.map (algebraMap K Ω)).roots, R', hR', ?_, ?_⟩
    · rw [← hr, ← roots_mul (hmul ▸ hm.ne_zero), ← hmul]
    · exact (hs.of_dvd hm.ne_zero ⟨_, by rw [hmul, mul_comm]⟩).eq_prod_roots_of_monic
        (hGm.of_mul_monic_left (hmul ▸ hm))
  obtain ⟨a', P', hP1, hP2, hP3⟩ := key a P x hx hG hP
  obtain ⟨b', Q', hQ1, hQ2, hQ3⟩ := key b Q y hy hGy hQ
  have hxr : x ∈ (G.map (algebraMap K Ω)).roots := by
    rw [mem_roots hGm.ne_zero, IsRoot.def, eval_map_algebraMap]; exact minpoly.aeval K x
  have hlt : a'.card < n := by
    have := Multiset.card_pos_iff_exists_mem.2 ⟨x, hxr⟩
    rw [← hn, hP2, Multiset.card_add]; omega
  rw [hP1, hQ1, ih _ hlt a' b' P' Q' rfl hP3 hQ3 fun H => ?_]
  have := h H
  rw [hP2, hQ2, Multiset.countP_add, Multiset.countP_add] at this
  omega

section Normed

variable {K Ω : Type} [NontriviallyNormedField K] [NormedField Ω] [NormedAlgebra K Ω]

theorem norm_prod_add [DecidableEq Ω] (a : Multiset Ω) (g : Ω → Ω) (t : K) :
    ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖t‖ ^ a.countP (fun x => g x = 0) *
        ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons x a ih =>
    by_cases hx : g x = 0
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_pos _ (by exact hx), Multiset.filter_cons_of_neg _ (by simpa using hx), hx,
        zero_add, norm_algebraMap']
      ring
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, ih,
        Multiset.countP_cons_of_neg _ (by exact hx), Multiset.filter_cons_of_pos _ (by exact hx),
        Multiset.map_cons, Multiset.prod_cons, norm_mul]
      ring

theorem countP_le [DecidableEq Ω] (a b : Multiset Ω) (g : Ω → Ω)
    (h : ∀ t : K, ‖(a.map fun x => g x + algebraMap K Ω t).prod‖ =
      ‖(b.map fun x => g x + algebraMap K Ω t).prod‖) :
    b.countP (fun x => g x = 0) ≤ a.countP (fun x => g x = 0) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
  set A : K → ℝ := fun t =>
    ‖((a.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hA
  set B : K → ℝ := fun t =>
    ‖((b.filter fun x => ¬ g x = 0).map fun x => g x + algebraMap K Ω t).prod‖ with hB
  have hc : ∀ c : Multiset Ω, Continuous fun t : K =>
      ‖(c.map fun x => g x + algebraMap K Ω t).prod‖ := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_const.add (continuous_algebraMap K Ω)).norm
  have hAc : Continuous A := hc _
  have hBc : Continuous fun t : K => ‖t‖ ^ (k + 1) * B t := (continuous_norm.pow _).mul (hc _)
  have heq : Set.EqOn A (fun t : K => ‖t‖ ^ (k + 1) * B t) {0}ᶜ := by
    intro t ht
    have ht0 : ‖t‖ ≠ 0 := norm_ne_zero_iff.2 ht
    have := h t
    rw [norm_prod_add a, norm_prod_add b, hk, add_assoc, pow_add, _root_.mul_assoc] at this
    exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
  have h0 := congrFun (Continuous.ext_on (dense_compl_singleton (0 : K)) hAc hBc heq) 0
  simp only [hA, norm_zero, pow_succ, mul_zero, zero_mul, map_zero, add_zero, norm_eq_zero,
    Multiset.prod_eq_zero_iff, Multiset.mem_map, Multiset.mem_filter] at h0
  obtain ⟨x, ⟨-, hx⟩, hx'⟩ := h0
  exact hx hx'

end Normed

section Padic

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem card_eq (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] Ω] (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖) :
    a.card = b.card := by
  have h1 := h (C (l : ℤ))
  have hl : ‖(l : Ω)‖ = ‖(l : ℚ_[l])‖ := by
    rw [← norm_algebraMap' Ω (l : ℚ_[l]), map_natCast]
  simp only [aeval_C, map_natCast, Multiset.map_const', Multiset.prod_replicate, norm_pow,
    hl] at h1
  refine pow_right_injective₀ ?_ ?_ h1
  · exact norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · exact Padic.norm_p_lt_one.ne

theorem rat_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ[X]) :
    ‖(a.map fun x => aeval x (F.map (algebraMap ℚ ℚ_[l]))).prod‖ =
      ‖(b.map fun x => aeval x (F.map (algebraMap ℚ ℚ_[l]))).prod‖ := by
  obtain ⟨d, hd, hF⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) F
  set F₀ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) F
  have hd0 : ((d : ℚ_[l])) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hd)
  have hx : ∀ x : Ω, aeval x F₀ =
      algebraMap ℚ_[l] Ω (d : ℚ_[l]) * aeval x (F.map (algebraMap ℚ ℚ_[l])) := by
    intro x
    have h1 : F₀.map (algebraMap ℤ ℚ_[l]) = C (d : ℚ_[l]) * F.map (algebraMap ℚ ℚ_[l]) := by
      have := congrArg (Polynomial.map (algebraMap ℚ ℚ_[l])) hF
      rw [Polynomial.map_map, zsmul_eq_mul, Polynomial.map_mul, Polynomial.map_intCast] at this
      rw [← C_eq_intCast] at this
      rw [← this]
      congr 1
    rw [← aeval_map_algebraMap ℚ_[l], h1, map_mul, aeval_C]
  have h1 := h F₀
  simp only [hx, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, norm_mul,
    norm_pow, norm_algebraMap', card_eq l a b h] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.2 hd0)) h1

theorem padic_case (a b : Multiset Ω)
    (h : ∀ F : ℤ[X], ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖)
    (F : ℚ_[l][X]) :
    ‖(a.map fun x => aeval x F).prod‖ = ‖(b.map fun x => aeval x F).prod‖ := by
  set n := F.natDegree + 1
  let φ : Multiset Ω → (Fin n → ℚ_[l]) → ℝ := fun c v =>
    ‖(c.map fun x => ∑ i : Fin n, algebraMap ℚ_[l] Ω (v i) * x ^ (i : ℕ)).prod‖
  have hc : ∀ c, Continuous (φ c) := fun c =>
    (continuous_multiset_prod c fun x _ => continuous_finsetSum _ fun i _ =>
      ((continuous_algebraMap ℚ_[l] Ω).comp (continuous_apply i)).mul continuous_const).norm
  have hd : DenseRange (Pi.map (fun (_ : Fin n) => ((↑) : ℚ → ℚ_[l]))) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have heq : φ a = φ b := by
    refine Continuous.ext_on hd (hc a) (hc b) ?_
    rintro _ ⟨v, rfl⟩
    have := rat_case (l := l) a b h (∑ i : Fin n, monomial (i : ℕ) (v i))
    simpa [φ, Polynomial.map_sum, aeval_monomial] using this
  have := congrFun heq fun i => F.coeff i
  have hx : ∀ x : Ω, aeval x F = ∑ i : Fin n, algebraMap ℚ_[l] Ω (F.coeff i) * x ^ (i : ℕ) := by
    intro x
    rw [aeval_eq_sum_range, Finset.sum_range]
    simp only [Algebra.smul_def]
    rfl
  simpa only [hx] using this

end Padic

end ResultantNorm

theorem eq_of_norm_resultant_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by
  intro l _ Ω _ _ _ a b P Q hP hQ h
  classical
  letI : NormedField Ω := spectralNorm.normedField ℚ_[l] Ω
  letI : NormedAlgebra ℚ_[l] Ω := spectralNorm.normedAlgebra ℚ_[l] Ω
  have h1 : ∀ F : Polynomial ℤ, ‖(a.map fun x => Polynomial.aeval x F).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x F).prod‖ := by
    intro F
    obtain ⟨u, hu⟩ := ResultantNorm.exists_prod_aeval a P hP (F.map (algebraMap ℤ ℚ_[l]))
    obtain ⟨v, hv⟩ := ResultantNorm.exists_prod_aeval b Q hQ (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at hu hv
    rw [← hu, ← hv, norm_algebraMap', norm_algebraMap']
    exact h F u v hu hv
  refine ResultantNorm.eq_of_countP _ a b P Q rfl hP hQ fun G => ?_
  have h2 : ∀ t : ℚ_[l],
      ‖(a.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ =
      ‖(b.map fun x => Polynomial.aeval x G + algebraMap ℚ_[l] Ω t).prod‖ := by
    intro t
    simpa only [map_add, Polynomial.aeval_C] using
      ResultantNorm.padic_case (l := l) a b h1 (G + Polynomial.C t)
  exact le_antisymm (ResultantNorm.countP_le b a _ fun t => (h2 t).symm)
    (ResultantNorm.countP_le a b _ h2)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ_[l] Ω] [Algebra.IsAlgebraic ℚ_[l] Ω] (a b : Multiset Ω) (P Q : Polynomial ℚ_[l]), P.map (algebraMap ℚ_[l] Ω) = (a.map fun x => Polynomial.X - Polynomial.C x).prod → Q.map (algebraMap ℚ_[l] Ω) = (b.map fun x => Polynomial.X - Polynomial.C x).prod → (∀ (F : Polynomial ℤ) (u v : ℚ_[l]), algebraMap ℚ_[l] Ω u = (a.map fun x => Polynomial.aeval x F).prod → algebraMap ℚ_[l] Ω v = (b.map fun x => Polynomial.aeval x F).prod → ‖u‖ = ‖v‖) → P = Q := by
  atlas_forward_decl GlobalTheory.eq_of_norm_resultant_eq
end

section
open Polynomial

namespace GlobalTheory.PolyNorm

noncomputable def ev {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K : Type} [CommRing K] [Algebra ℚ K]
    (F : K[X]) : K :=
  MvPolynomial.aeval (fun i : Fin r => F.coeff i) Φ

noncomputable def gen {r : ℕ} {K : Type} [CommRing K] (f : Fin r → K) : K[X] :=
  ∑ i : Fin r, monomial (i : ℕ) (f i)

theorem ev_map {r : ℕ} (Φ : MvPolynomial (Fin r) ℚ) {K L : Type} [CommRing K] [Algebra ℚ K]
    [CommRing L] [Algebra ℚ L] (φ : K →+* L) (F : K[X]) : φ (ev Φ F) = ev Φ (F.map φ) := by
  unfold ev
  rw [MvPolynomial.map_aeval, MvPolynomial.aeval_def, MvPolynomial.coe_eval₂Hom]
  congr 1
  · exact RingHom.ext_rat _ _
  · ext i; simp

theorem gen_map {r : ℕ} {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f : Fin r → K) :
    (gen f).map φ = gen (fun i => φ (f i)) := by
  simp [gen, Polynomial.map_sum]

theorem gen_coeff {r : ℕ} {K : Type} [CommRing K] (F : K[X]) (h : F.natDegree < r) :
    gen (fun i : Fin r => F.coeff i) = F := by
  unfold gen
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (F.coeff i)) r]
  exact (as_sum_range' F r h).symm

theorem natDegree_gen {r : ℕ} {K : Type} [CommRing K] (f : Fin (r + 1) → K) :
    (gen f).natDegree ≤ r := by
  unfold gen
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => (natDegree_monomial_le _).trans ?_
  exact Nat.lt_succ_iff.mp i.2

theorem ev_homog {r m : ℕ} {Φ : MvPolynomial (Fin r) ℚ} (h : Φ.IsHomogeneous m)
    {K : Type} [CommRing K] [Algebra ℚ K] (c : K) (F : K[X]) :
    ev Φ (C c * F) = c ^ m * ev Φ F := by
  unfold ev
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
    MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : ∑ i, d i = m := by
    have := h.degree_eq_sum_deg_support hd
    rw [this]
    exact (Finset.sum_subset (Finset.subset_univ _) (by simp)).symm
  simp only [coeff_C_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd']
  ring

section
variable (N : ℤ[X] → ℚ) (Φ : (r : ℕ) → MvPolynomial (Fin r) ℚ)
  (hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)))
include hN

theorem shift_poly (F : ℤ[X]) : ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ) := by
  refine ⟨ev (Φ (F.natDegree + 1)) (F.map (Int.castRingHom ℚ[X]) + C X), fun t => ?_⟩
  rw [hN (F.natDegree + 1), ← coe_evalRingHom, ev_map]
  · congr 1
    simp [Polynomial.map_map, RingHom.ext_int ((evalRingHom (t:ℚ)).comp _) (Int.castRingHom ℚ)]
  · rw [← C_eq_natCast, natDegree_add_C]; omega

theorem shift_poly₂ (F G : ℤ[X]) :
    ∃ p : ℚ[X], ∀ t : ℕ, N ((F + t) * (G + t)) = p.eval (t : ℚ) := by
  refine ⟨ev (Φ (F.natDegree + G.natDegree + 1)) ((F.map (Int.castRingHom ℚ[X]) + C X) *
    (G.map (Int.castRingHom ℚ[X]) + C X)), fun t => ?_⟩
  rw [hN (F.natDegree + G.natDegree + 1), ← coe_evalRingHom, ev_map]
  · congr 1
    simp [Polynomial.map_map, RingHom.ext_int ((evalRingHom (t:ℚ)).comp _) (Int.castRingHom ℚ)]
  · refine lt_of_le_of_lt natDegree_mul_le ?_
    rw [← C_eq_natCast, natDegree_add_C, natDegree_add_C]; omega

theorem mul_all (Good : ℤ[X] → Prop) (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hm : ∀ F G, Good F → Good G → N (F * G) = N F * N G) (F G : ℤ[X]) :
    N (F * G) = N F * N G := by
  obtain ⟨p, hp⟩ := shift_poly N Φ hN F
  obtain ⟨q, hq⟩ := shift_poly N Φ hN G
  obtain ⟨s, hs⟩ := shift_poly₂ N Φ hN F G
  have : s = p * q := by
    apply eq_of_infinite_eval_eq
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp ((hG F).and (hG G))
    refine Set.Infinite.mono (s := (fun t : ℕ => (t : ℚ)) '' Set.Ici a) ?_
      ((Set.Ici_infinite a).image Nat.cast_injective.injOn)
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_setOf_eq, eval_mul]
    rw [← hp, ← hq, ← hs, hm _ _ (ha t ht).1 (ha t ht).2]
  have h0 := hs 0
  rw [this, eval_mul, ← hp, ← hq] at h0
  simpa using h0

theorem ev_mul (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K] [Algebra ℚ K]
    (r₁ r₂ s : ℕ) (hs : r₁ + r₂ < s) (F G : K[X]) (hF : F.natDegree ≤ r₁)
    (hG : G.natDegree ≤ r₂) :
    ev (Φ s) (F * G) = ev (Φ (r₁ + 1)) F * ev (Φ (r₂ + 1)) G := by
  let R := MvPolynomial (Fin (r₁ + 1) ⊕ Fin (r₂ + 1)) ℚ
  let A : R[X] := gen fun i => MvPolynomial.X (Sum.inl i)
  let B : R[X] := gen fun i => MvPolynomial.X (Sum.inr i)
  have key : ev (Φ s) (A * B) = ev (Φ (r₁ + 1)) A * ev (Φ (r₂ + 1)) B := by
    apply MvPolynomial.funext_set (s := fun _ => Set.range (Int.cast : ℤ → ℚ))
      (fun _ => Set.infinite_range_of_injective Int.cast_injective)
    intro x hx
    choose y hy using fun i => hx i (Set.mem_univ i)
    have hA : A.map (MvPolynomial.eval x) =
        (gen fun i => y (Sum.inl i)).map (Int.castRingHom ℚ) := by
      simp [A, gen_map, hy]
    have hB : B.map (MvPolynomial.eval x) =
        (gen fun i => y (Sum.inr i)).map (Int.castRingHom ℚ) := by
      simp [B, gen_map, hy]
    have h1 := natDegree_gen fun i => y (Sum.inl i)
    have h2 := natDegree_gen fun i => y (Sum.inr i)
    rw [map_mul, ev_map, ev_map, ev_map, Polynomial.map_mul, hA, hB, ← Polynomial.map_mul,
      ← hN, ← hN, ← hN, hm]
    · omega
    · omega
    · exact lt_of_le_of_lt natDegree_mul_le (by omega)
  let φ : R →+* K := (MvPolynomial.aeval
    (Sum.elim (fun i : Fin (r₁ + 1) => F.coeff i) (fun i : Fin (r₂ + 1) => G.coeff i))).toRingHom
  have hA : A.map φ = F := by
    refine (gen_map _ _).trans (Eq.trans ?_ (gen_coeff F (Nat.lt_succ_of_le hF)))
    congr 1
    exact funext fun i => MvPolynomial.aeval_X _ _
  have hB : B.map φ = G := by
    refine (gen_map _ _).trans (Eq.trans ?_ (gen_coeff G (Nat.lt_succ_of_le hG)))
    congr 1
    exact funext fun i => MvPolynomial.aeval_X _ _
  have := congrArg φ key
  rwa [map_mul, ev_map, ev_map, ev_map, Polynomial.map_mul, hA, hB] at this

theorem ev_one (h1 : N 1 = 1) {K : Type} [CommRing K] [Algebra ℚ K] (r : ℕ) :
    ev (Φ (r + 1)) (1 : K[X]) = 1 := by
  have := ev_map (Φ (r + 1)) (algebraMap ℚ K) ((1 : ℤ[X]).map (Int.castRingHom ℚ))
  rw [← hN _ _ (by simp), h1] at this
  simpa using this.symm

theorem ev_compat (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) {K : Type} [CommRing K]
    [Algebra ℚ K] (s : ℕ) (F : K[X]) (hF : F.natDegree < s) :
    ev (Φ s) F = ev (Φ (F.natDegree + 1)) F := by
  have := ev_mul N Φ hN hm F.natDegree 0 s hF F 1 le_rfl (by simp)
  rwa [ev_one N Φ hN h1, mul_one, mul_one] at this

theorem exists_ext (h1 : N 1 = 1) (hm : ∀ F G, N (F * G) = N F * N G) (K : Type) [CommRing K]
    [Algebra ℚ K] : ∃ M : K[X] →* K, ∀ s (F : K[X]), F.natDegree < s → M F = ev (Φ s) F := by
  refine ⟨⟨⟨fun F => ev (Φ (F.natDegree + 1)) F, ev_one N Φ hN h1 _⟩, fun F G => ?_⟩,
    fun s F h => (ev_compat N Φ hN h1 hm s F h).symm⟩
  dsimp only
  rw [← ev_mul N Φ hN hm F.natDegree G.natDegree _ (Nat.lt_succ_self _) F G le_rfl le_rfl,
    ← ev_compat N Φ hN h1 hm]
  exact Nat.lt_succ_of_le natDegree_mul_le

end

theorem monic_ev {m : ℕ} {Φ : MvPolynomial (Fin 2) ℚ} (h : Φ.IsHomogeneous m)
    (h1 : ev Φ (1 : ℚ[X]) = 1) :
    (ev Φ (C X - X : ℚ[X][X])).Monic ∧ (ev Φ (C X - X : ℚ[X][X])).natDegree = m := by
  have hd : ∀ d ∈ Φ.support, d 0 + d 1 = m := fun d hd => by
    have := h.degree_eq_sum_deg_support hd
    rw [this, ← Fin.sum_univ_two (fun i => d i)]
    exact (Finset.sum_subset (Finset.subset_univ _) (by simp)).symm
  have e : ev Φ (C X - X : ℚ[X][X]) =
      ∑ d ∈ Φ.support, monomial (d 0) (Φ.coeff d * (-1) ^ d 1) := by
    unfold ev
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [← C_mul_X_pow_eq_monomial, coeff_X, coeff_C]
    ring
  have hle : (ev Φ (C X - X : ℚ[X][X])).natDegree ≤ m := by
    rw [e]
    refine natDegree_sum_le_of_forall_le _ _ fun d hd' => (natDegree_monomial_le _).trans ?_
    have := hd d hd'; omega
  have hc : (ev Φ (C X - X : ℚ[X][X])).coeff m = 1 := by
    rw [e, ← h1, finset_sum_coeff]
    unfold ev
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine Finset.sum_congr rfl fun d hd' => ?_
    have := hd d hd'
    by_cases h0 : d 1 = 0
    · have : d 0 = m := by omega
      simp [coeff_monomial, h0, this]
    · have : d 0 ≠ m := by omega
      simp [coeff_monomial, h0, this, coeff_one]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one m hle hc,
    natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hc])⟩

theorem eq_prod_of_mul {K : Type} [Field K] [IsAlgClosed K] (M : K[X] →* K) (a : Multiset K)
    (hc : ∀ c, M (C c) = c ^ Multiset.card a)
    (hl : ∀ β, M (C β - X) = (a.map fun x => β - x).prod) (F : K[X]) :
    M F = (a.map fun x => F.eval x).prod := by
  let M' : K[X] →* K :=
    { toFun := fun F => (a.map fun x => F.eval x).prod
      map_one' := by simp
      map_mul' := by simp [Multiset.prod_map_mul] }
  have hc' : ∀ c, M (C c) = M' (C c) := fun c => by simp [hc, M']
  have hl' : ∀ β, M (X - C β) = M' (X - C β) := fun β => by
    have : (X - C β : K[X]) = C (-1) * (C β - X) := by simp
    rw [this, map_mul, map_mul, hc', hl]
    simp [M']
  change M F = M' F
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := F) IsAlgClosed.card_roots_eq_natDegree,
    map_mul, map_mul, hc', map_multiset_prod, map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  simp [hl']

theorem norm_all {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (U : Matrix (Fin m) (Fin m) ℤ_[l])
    (N : ℤ[X] → ℚ) (Good : ℤ[X] → Prop)
    (hp : ∀ F : ℤ[X], ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ))
    (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hn : ∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) (F : ℤ[X]) :
    ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖ := by
  obtain ⟨p, hp⟩ := hp F
  have t0 : Filter.Tendsto (fun k : ℕ => (l : ℤ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.out.one_lt))
  have c1 : Continuous fun x : ℤ_[l] => ‖(p.map (Rat.castHom ℚ_[l])).eval (x : ℚ_[l])‖ :=
    ((p.map (Rat.castHom ℚ_[l])).continuous.comp continuous_subtype_val).norm
  have c2 : Continuous fun x : ℤ_[l] =>
      ‖(Polynomial.aeval U F + x • (1 : Matrix (Fin m) (Fin m) ℤ_[l])).det‖ :=
    ((continuous_const.add (continuous_id.smul continuous_const)).matrix_det).norm
  have e1 : ∀ t : ℕ, ((N (F + t) : ℚ) : ℚ_[l]) =
      (p.map (Rat.castHom ℚ_[l])).eval (((t : ℤ_[l])) : ℚ_[l]) := fun t => by
    rw [hp, PadicInt.coe_natCast, ← map_natCast (Rat.castHom ℚ_[l]), eval_map, eval₂_at_apply]
    rfl
  have e2 : ∀ t : ℕ, Polynomial.aeval U (F + (t : ℤ[X])) =
      Polynomial.aeval U F + (t : ℤ_[l]) • (1 : Matrix (Fin m) (Fin m) ℤ_[l]) := fun t => by
    rw [map_add, map_natCast, Nat.cast_smul_eq_nsmul, nsmul_one]
  have h := tendsto_nhds_unique_of_eventuallyEq ((c1.tendsto 0).comp t0) ((c2.tendsto 0).comp t0)
    (((tendsto_pow_atTop_atTop_of_one_lt hl.out.one_lt).eventually (hG F)).mono fun k hk => by
      have := hn _ hk
      rw [e1, e2] at this
      simpa using this)
  have := e1 0
  simp only [Nat.cast_zero, add_zero] at this
  rw [this, h]
  simp

theorem det_eq_prod {K : Type} [Field K] [IsAlgClosed K] {m : ℕ} (V : Matrix (Fin m) (Fin m) K)
    (b : Multiset K) (hb : V.charpoly = (b.map fun x => X - C x).prod) (F : K[X]) :
    (aeval V F).det = (b.map fun x => F.eval x).prod := by
  have hc : Multiset.card b = m := by
    rw [← natDegree_multiset_prod_X_sub_C_eq_card b, ← hb]; simp
  refine eq_prod_of_mul (Matrix.detMonoidHom.comp (aeval V : K[X] →ₐ[K] _).toMonoidHom) b
    (fun c => ?_) (fun β => ?_) F
  · simp [hc, Algebra.algebraMap_eq_smul_one]
  · have := congrArg (eval β) hb
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at this
    simpa [Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def] using this

theorem eq_det : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (N : Polynomial ℤ → ℚ) (Good : Polynomial ℤ → Prop), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous m ∧ ∀ a : Fin r → ℤ, N (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → N 1 = 1 → (∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t)) → (∀ F G, Good F → Good G → N (F * G) = N F * N G) → (∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) → ∀ F, ((N F : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m U N Good hΦ h1 hG hm hn
  choose Φ hh hΦ using hΦ
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → N F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    rw [show ∑ i : Fin r, monomial (i : ℕ) (F.coeff i) = F from gen_coeff F hF] at this
    rw [this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have hm' := mul_all N Φ hN Good hG hm
  have hn' := norm_all U N Good (shift_poly N Φ hN) hG hn
  obtain ⟨E, _, _, _, _⟩ : ∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[l] E),
      IsAlgClosed E ∧ Algebra.IsAlgebraic ℚ_[l] E :=
    ⟨AlgebraicClosure ℚ_[l], inferInstance, inferInstance, inferInstance, inferInstance⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[l] E).injective
  have inj : Function.Injective (algebraMap ℚ_[l] E) := (algebraMap ℚ_[l] E).injective
  obtain ⟨M, hM⟩ := exists_ext N Φ hN h1 hm' E
  obtain ⟨hP, hPd⟩ := monic_ev (hh 2) (ev_one N Φ hN h1 1)
  set P := ev (Φ 2) (C X - X : ℚ[X][X]) with hPdef
  let ψ : ℤ_[l] →+* E := (algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom
  let V : Matrix (Fin m) (Fin m) E := U.map ψ
  have roots : ∀ S : E[X], S.Monic → S = (S.roots.map fun x => X - C x).prod := fun S hS =>
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hS IsAlgClosed.card_roots_eq_natDegree).symm
  let a := (P.map (algebraMap ℚ E)).roots
  have ha : P.map (algebraMap ℚ E) = (a.map fun x => X - C x).prod := roots _ (hP.map _)
  have hac : Multiset.card a = m := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = (a.map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M a (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← mul_one (C c), ev_homog (hh 1), ev_one N Φ hN h1, mul_one, hac]
    · have := congrArg (eval β) ha
      rw [eval_multiset_prod, Multiset.map_map, eval_map, ← coe_eval₂RingHom, hPdef,
        ev_map] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  have hNa : ∀ F : ℤ[X], algebraMap ℚ_[l] E (N F : ℚ_[l]) = (a.map fun x => aeval x F).prod := by
    intro F
    have := hMa (F.map (algebraMap ℤ E))
    simp only [eval_map_algebraMap] at this
    rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le), map_ratCast,
      ← eq_ratCast (algebraMap ℚ E), hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
    congr 2
    all_goals exact RingHom.ext_int _ _
  have hDb : ∀ b : Multiset E, V.charpoly = (b.map fun x => X - C x).prod → ∀ F : ℤ[X],
      algebraMap ℚ_[l] E ((aeval U F).det : ℤ_[l]) = (b.map fun x => aeval x F).prod := by
    intro b hb F
    have := det_eq_prod V b hb (F.map (algebraMap ℤ E))
    simp only [eval_map_algebraMap, aeval_map_algebraMap] at this
    rw [← this]
    change ψ _ = _
    rw [RingHom.map_det]
    congr 1
    exact (aeval_algHom_apply ψ.mapMatrix.toIntAlgHom U F).symm
  have hPm : (P.map (Rat.castHom ℚ_[l])).map (algebraMap ℚ_[l] E) = P.map (algebraMap ℚ E) := by
    rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_rat _ _
  have hQm : (U.charpoly.map PadicInt.Coe.ringHom).map (algebraMap ℚ_[l] E) = V.charpoly := by
    rw [Polynomial.map_map, ← Matrix.charpoly_map]
  have hb := roots _ V.charpoly_monic
  have key := GlobalTheory.T.eq_of_norm_prod_aeval_eq_moduli l E a V.charpoly.roots (P.map (Rat.castHom ℚ_[l]))
    (U.charpoly.map PadicInt.Coe.ringHom) (hPm.trans ha) (hQm.trans hb) (fun F u v hu hv => by
      rw [← hNa] at hu
      rw [← hDb _ hb] at hv
      rw [inj hu, inj hv, hn']
      rfl)
  intro F
  apply inj
  rw [hNa, hDb a]
  rw [← hQm, ← key, hPm, ha]

end GlobalTheory.PolyNorm
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace SquareDensity

theorem exists_sq_add_sub_dvd {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∃ w : R, x ∣ w ∧ x ^ n ∣ w ^ 2 + w - x := by
  induction n with
  | zero => exact ⟨0, dvd_zero _, by simp⟩
  | succ n ih =>
    obtain ⟨w, ⟨c, hc⟩, hw⟩ := ih
    refine ⟨x - w ^ 2, ⟨1 - c * w, by rw [hc]; ring⟩, ?_⟩
    have h : (x - w ^ 2) ^ 2 + (x - w ^ 2) - x = (w ^ 2 + w - x) * (x * (c * w - c - 1)) := by
      have : x * (c * w - c - 1) = w ^ 2 - w - x := by rw [hc]; ring
      rw [this]; ring
    rw [h, pow_succ]
    exact mul_dvd_mul hw (dvd_mul_right _ _)

theorem dvd_aeval_sub_aeval {K S σ : Type*} [CommRing K] [CommRing S] [Algebra K S]
    (Φ : MvPolynomial σ K) (s : S) (a b : σ → S) (h : ∀ i, s ∣ a i - b i) :
    s ∣ MvPolynomial.aeval a Φ - MvPolynomial.aeval b Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    simp only [map_add]
    convert this using 1
    ring
  | mul_X p i hp =>
    have := dvd_add (hp.mul_right (a i)) ((h i).mul_left (MvPolynomial.aeval b p))
    simp only [map_mul, MvPolynomial.aeval_X]
    convert this using 1
    ring

theorem eval_aeval {K σ : Type*} [CommRing K] (Φ : MvPolynomial σ K) (a : σ → Polynomial K)
    (t : K) :
    (MvPolynomial.aeval a Φ).eval t = MvPolynomial.eval (fun i => (a i).eval t) Φ := by
  induction Φ using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem eq_zero_of_sq {K : Type*} [Field K] [CharZero K] (Ψ : Polynomial ℤ → K) (d : ℕ)
    (hΨ : ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) K, Φ.totalDegree ≤ d ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        Ψ F = MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ)
    (hsq : ∀ G, Ψ (G ^ 2) = 0) (F : Polynomial ℤ) : Ψ F = 0 := by
  set x : Polynomial (Polynomial ℤ) :=
    Polynomial.C Polynomial.X * (F - 1).map Polynomial.C with hx
  obtain ⟨w, -, hw⟩ := exists_sq_add_sub_dvd x (d + 1)
  set y : Polynomial (Polynomial ℤ) := 1 + 2 * w with hy
  obtain ⟨Φ, hd, hΦ⟩ := hΨ (max F.natDegree (y ^ 2).natDegree + 1)
  set a : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((1 + 4 * x).coeff i).map (Int.castRingHom K) with ha
  set b : Fin (max F.natDegree (y ^ 2).natDegree + 1) → Polynomial K :=
    fun i => ((y ^ 2).coeff i).map (Int.castRingHom K) with hb
  have hai : ∀ i, a i = Polynomial.C (((1 : Polynomial ℤ).coeff i : ℤ) : K) +
      Polynomial.C (4 * (((F - 1).coeff i : ℤ) : K)) * Polynomial.X := by
    intro i
    have h4 : (4 : Polynomial (Polynomial ℤ)) = Polynomial.C 4 := rfl
    simp only [ha, hx, h4, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_one]
    split_ifs <;> simp [Polynomial.map_mul, map_ofNat] <;> ring
  have hb0 : MvPolynomial.aeval b Φ = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (k : K))
      Int.cast_injective fun k => ?_
    show (MvPolynomial.aeval b Φ).eval (k : K) = 0
    rw [eval_aeval, ← hsq (y.map (Polynomial.evalRingHom k)), ← Polynomial.map_pow, hΦ]
    · congr 2
      funext i
      simp only [hb, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
      exact Polynomial.eval_intCast_map (Int.castRingHom K) _ k
    · exact lt_of_le_of_lt (Polynomial.natDegree_map_le.trans (le_max_right _ _))
        (Nat.lt_succ_self _)
  have hdvd : (Polynomial.X : Polynomial K) ^ (d + 1) ∣ MvPolynomial.aeval a Φ := by
    rw [← sub_zero (MvPolynomial.aeval a Φ), ← hb0]
    apply dvd_aeval_sub_aeval
    intro i
    have h1 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (d + 1)) ∣ (1 + 4 * x) - y ^ 2 := by
      have h2 : (1 + 4 * x) - y ^ 2 = (w ^ 2 + w - x) * (-4) := by rw [hy]; ring
      rw [h2, map_pow]
      exact ((pow_dvd_pow_of_dvd (dvd_mul_right _ _) _).trans hw).mul_right _
    have h3 := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 h1 i
    have h4 := Polynomial.map_dvd (Int.castRingHom K) h3
    simpa only [Polynomial.map_pow, Polynomial.map_X, Polynomial.coeff_sub,
      Polynomial.map_sub] using h4
  have hdeg : (MvPolynomial.aeval a Φ).natDegree ≤ d * 1 := by
    refine MvPolynomial.aeval_natDegree_le Φ hd a fun i => ?_
    rw [hai]
    compute_degree
  have ha0 : MvPolynomial.aeval a Φ = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (by
      rw [Polynomial.natDegree_X_pow]; omega)
  have h := eval_aeval Φ a (1 / 4)
  rw [ha0, Polynomial.eval_zero] at h
  rw [hΦ F (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _)), h]
  congr 2
  funext i
  rw [hai]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.coeff_sub, Int.cast_sub]
  ring

theorem eq_sum_monomial (F : Polynomial ℤ) (r : ℕ) (h : F.natDegree < r) :
    F = ∑ i : Fin r, Polynomial.monomial (i : ℕ) (F.coeff i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (F.coeff i)) r]
  exact F.as_sum_range' r h

theorem exists_det_polynomial {R K : Type*} [CommRing R] [CommRing K] (φ : R →+* K) {m : ℕ}
    (U : Matrix (Fin m) (Fin m) R) (r : ℕ) :
    ∃ Φ : MvPolynomial (Fin r) K, Φ.IsHomogeneous m ∧
      ∀ F : Polynomial ℤ, F.natDegree < r →
        φ (Polynomial.aeval U F).det =
          MvPolynomial.eval (fun i : Fin r => ((F.coeff i : ℤ) : K)) Φ := by
  let M : Matrix (Fin m) (Fin m) (MvPolynomial (Fin r) K) := fun j k =>
    ∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i
  have hM : ∀ j k, (M j k).IsHomogeneous 1 := fun j k =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => (MvPolynomial.isHomogeneous_X K i).C_mul _
  refine ⟨M.det, ?_, fun F hF => ?_⟩
  · rw [Matrix.det_apply']
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun σ _ => ?_
    have h1 := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => M (σ i) i) (fun _ => 1)
      fun i _ => hM _ _
    have h2 := h1.C_mul (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : K)
    simpa using h2
  · rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext j k
    rw [Polynomial.aeval_eq_sum_range' hF, ← Fin.sum_univ_eq_sum_range
      (fun i => F.coeff i • U ^ i) r]
    change φ ((∑ i : Fin r, F.coeff i • U ^ (i : ℕ)) j k) = MvPolynomial.eval _
      (∑ i : Fin r, MvPolynomial.C (φ ((U ^ (i : ℕ)) j k)) * MvPolynomial.X i)
    rw [Matrix.sum_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.smul_apply, map_zsmul, zsmul_eq_mul, mul_comm, map_mul, MvPolynomial.eval_C,
      MvPolynomial.eval_X]

end SquareDensity

theorem sq_eq_det_aeval_of_sq : ∀ (l : ℕ) [Fact l.Prime] (m g : ℕ) (U : Matrix (Fin m) (Fin m) ℤ_[l]) (D : Polynomial ℤ → ℚ), (∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous g ∧ ∀ a : Fin r → ℤ, D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ) → (∀ G, ((D (G ^ 2) : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l])) → (∀ F H, Polynomial.aeval U H = 0 → D (F + H) = D F) → ∀ F, ((D F ^ 2 : ℚ) : ℚ_[l]) = ((Polynomial.aeval U F).det : ℤ_[l]) := by
  intro l _ m g U D hD hsq _ F
  refine sub_eq_zero.1 (SquareDensity.eq_zero_of_sq
    (fun F => ((D F ^ 2 : ℚ) : ℚ_[l]) - ((Polynomial.aeval U F).det : ℤ_[l]))
    (max (2 * g) m) (fun r => ?_) (fun G => ?_) F)
  · obtain ⟨Φ, hΦ, hDΦ⟩ := hD r
    obtain ⟨Θ, hΘ, hdet⟩ := SquareDensity.exists_det_polynomial (PadicInt.Coe.ringHom (p := l)) U r
    refine ⟨(MvPolynomial.map (algebraMap ℚ ℚ_[l]) Φ) ^ 2 - Θ, ?_, fun F hF => ?_⟩
    · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le_max ?_ hΘ.totalDegree_le)
      have := ((hΦ.map (algebraMap ℚ ℚ_[l])).pow 2).totalDegree_le
      rwa [mul_comm] at this
    · rw [map_sub, map_pow, ← hdet F hF, Rat.cast_pow]
      congr 2
      have h1 := hDΦ fun i => F.coeff i
      rw [← SquareDensity.eq_sum_monomial F r hF] at h1
      rw [h1, MvPolynomial.eval_map]
      have h2 := MvPolynomial.eval₂_comp_left (algebraMap ℚ ℚ_[l]) (RingHom.id ℚ)
        (fun i : Fin r => ((F.coeff i : ℤ) : ℚ)) Φ
      simpa [Function.comp_def] using h2
  · simp only [map_pow, Matrix.det_pow, Rat.cast_pow, hsq G, PadicInt.coe_pow, sub_self]

end GlobalTheory
end

section
section
namespace GlobalTheory.SectionCount
open Polynomial

def PolyHom (n : ℕ) (D : ℤ[X] → ℚ) : Prop :=
  ∀ r : ℕ, ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous n ∧ ∀ a : Fin r → ℤ,
    D (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) = MvPolynomial.eval (fun i => (a i : ℚ)) Φ

theorem PolyHom.div {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) (c : ℚ) : PolyHom n (fun F => D F / c) := by
  intro r
  obtain ⟨Φ, hΦ, hD⟩ := h r
  refine ⟨MvPolynomial.C c⁻¹ * Φ, ?_, fun a => ?_⟩
  · simpa using (MvPolynomial.isHomogeneous_C (Fin r) c⁻¹).mul hΦ
  · simp only [hD a, map_mul, MvPolynomial.eval_C]
    ring

theorem PolyHom.sq {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) : PolyHom (2 * n) (fun F => D (F ^ 2)) := by
  classical
  intro r
  obtain ⟨Φ, hΦ, hD⟩ := h (2 * r)
  let q : Fin (2 * r) → MvPolynomial (Fin r) ℚ := fun k =>
    ∑ i : Fin r, ∑ j : Fin r, if (i : ℕ) + j = k then MvPolynomial.X i * MvPolynomial.X j else 0
  have hq : ∀ k, (q k).IsHomogeneous 2 := by
    intro k
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X ℚ i).mul (MvPolynomial.isHomogeneous_X ℚ j)
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  refine ⟨MvPolynomial.aeval q Φ, hΦ.aeval q hq, fun a => ?_⟩
  let b : Fin (2 * r) → ℤ := fun k => ∑ i : Fin r, ∑ j : Fin r, if (i : ℕ) + j = k then a i * a j else 0
  have e : (∑ i : Fin r, Polynomial.monomial (i : ℕ) (a i)) ^ 2 =
      ∑ k : Fin (2 * r), Polynomial.monomial (k : ℕ) (b k) := by
    simp only [b, map_sum]
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_comm (γ := Fin (2 * r))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (γ := Fin (2 * r))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (⟨i + j, by omega⟩ : Fin (2 * r))]
    · simp [monomial_mul_monomial]
    · intro k _ hk
      rw [if_neg, map_zero]
      intro h'
      exact hk (Fin.ext h'.symm)
    · simp
  show D _ = _
  rw [e, hD b]
  have : (fun k => (b k : ℚ)) = fun k => MvPolynomial.eval (fun i => (a i : ℚ)) (q k) := by
    funext k
    simp only [b, q, map_sum, Int.cast_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [this, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eq_eval_map]
  have h2 : ((MvPolynomial.eval fun i => (a i : ℚ)).comp (algebraMap ℚ (MvPolynomial (Fin r) ℚ))) = RingHom.id ℚ := by
    ext x; simp
  rw [h2, MvPolynomial.map_id]
  rfl

theorem PolyHom.exists_shift {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) (F : ℤ[X]) :
    ∃ p : ℚ[X], ∀ t : ℕ, D (F + t) = p.eval (t : ℚ) := by
  classical
  obtain ⟨Φ, -, hD⟩ := h (F.natDegree + 1)
  refine ⟨MvPolynomial.aeval (fun i : Fin (F.natDegree + 1) =>
    (C (F.coeff i : ℚ) + if i = 0 then X else 0 : ℚ[X])) Φ, fun t => ?_⟩
  have e : F + t = ∑ i : Fin (F.natDegree + 1),
      Polynomial.monomial (i : ℕ) (F.coeff i + if i = 0 then (t : ℤ) else 0) := by
    simp only [map_add, Finset.sum_add_distrib]
    congr 1
    · conv_lhs => rw [F.as_sum_range]
      exact (Fin.sum_univ_eq_sum_range (fun i => monomial i (F.coeff i)) _).symm
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        rw [if_neg hk, map_zero]
      · simp
  rw [e, hD, ← Polynomial.coe_evalRingHom, MvPolynomial.aeval_def, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_eq_eval_map]
  have h2 : ((evalRingHom (t : ℚ)).comp (algebraMap ℚ ℚ[X])) = RingHom.id ℚ := by
    ext x; simp
  rw [h2, MvPolynomial.map_id]
  congr 2
  funext i
  by_cases hi : i = 0 <;> simp [hi]

theorem PolyHom.eq_of_eventually {n : ℕ} {D : ℤ[X] → ℚ} (h : PolyHom n D) (F G : ℤ[X])
    (e : ∀ᶠ t : ℕ in Filter.atTop, D (F + t) = D (G + t)) : D F = D G := by
  obtain ⟨p, hp⟩ := h.exists_shift F
  obtain ⟨q, hq⟩ := h.exists_shift G
  have : p = q := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 e
    refine Polynomial.eq_of_infinite_eval_eq p q ?_
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((N + k : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have := Nat.cast_injective (R := ℚ) hab
      omega
    · intro k
      show p.eval _ = q.eval _
      rw [← hp, ← hq]
      exact hN _ (by omega)
  have h1 := hp 0
  have h2 := hq 0
  simp only [Nat.cast_zero, add_zero] at h1 h2
  rw [h1, h2, this]

theorem aeval_eq_of_act {Q : Type} [AddCommGroup Q] (s : Module.End ℤ Q) (act : ℤ[X] → Q → Q)
    (h1 : ∀ x, act 1 x = x) (hadd : ∀ F G x, act (F + G) x = act F x + act G x)
    (hX : ∀ F x, act (X * F) x = s (act F x)) (F : ℤ[X]) (x : Q) : aeval s F x = act F x := by
  let φ : ℤ[X] →+ Q := AddMonoidHom.mk' (fun F => act F x) (fun F G => hadd F G x)
  have hp : ∀ n : ℕ, aeval s (X ^ n : ℤ[X]) x = act (X ^ n) x := by
    intro n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ', hX, ← ih]; simp
  induction F using Polynomial.induction_on' with
  | add p q hp' hq' => rw [map_add, LinearMap.add_apply, hp', hq', hadd]
  | monomial n a =>
    have : (monomial n a : ℤ[X]) = a • X ^ n := by
      rw [← C_mul_X_pow_eq_monomial, smul_eq_C_mul]
    rw [this, map_smul, LinearMap.smul_apply, hp]
    exact (map_zsmul φ a (X ^ n)).symm

end GlobalTheory.SectionCount

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
namespace GlobalTheory.SectionCount

variable {K : Type} [Field K] [IsAlgClosed K]

noncomputable def ptEnd (P : Out.PolAV (Sp K)) (s : P.A ⟶ P.A) [IsMonHom s] :
    Module.End ℤ (Additive (Out.baseOver (Sp K) ⟶ P.A)) :=
  (AddMonoidHom.mk' (fun x : Additive (Out.baseOver (Sp K) ⟶ P.A) =>
    Additive.ofMul (x.toMul ≫ s)) (fun x y => by
      rw [toMul_add, ← ofMul_mul, MonObj.mul_comp])).toIntLinearMap

theorem linComb_eq (P : Out.PolAV (Sp K)) {m : ℕ} (pt : Fin m → (Out.baseOver (Sp K) ⟶ P.A)) (c : Fin m → ℕ) :
    Additive.ofMul (Out.linComb pt c) = ∑ i, c i • Additive.ofMul (pt i) := by
  rw [Out.linComb, List.prod_ofFn, ofMul_prod]
  simp only [ofMul_pow]

theorem exists_matrix (hL : Out.Laws) (hL2 : Out.Laws2) (P : Out.PolAV (Sp K)) (s : P.A ⟶ P.A) [IsMonHom s]
    (l : ℕ) [Fact l.Prime] (hl : (l : K) ≠ 0) (ev : Polynomial ℤ → (P.A ⟶ P.A)) (h1 : ev 1 = 𝟙 P.A)
    (hadd : ∀ F G, ev (F + G) = ev F * ev G) (hX : ∀ F, ev (Polynomial.X * F) = ev F ≫ s) :
    ∃ U : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) ℤ_[l],
      (∀ F : Polynomial ℤ, Finite {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1} →
        ‖(Polynomial.aeval U F).det‖ =
          ‖((Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1} : ℕ) : ℚ_[l])‖) ∧
      (∀ F : Polynomial ℤ, Polynomial.aeval U F = 0 → ev F = 1) ∧
      ∀ (j : ℕ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A))
        (Mat : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j))),
        TorsBasis P.A (l ^ j) pt → ActsBy pt s Mat → PadicInt.toZModPow j U.det = Mat.det := by
  have hp : l.Prime := Fact.out
  have hact : ∀ (F : Polynomial ℤ) (x : Additive (Out.baseOver (Sp K) ⟶ P.A)),
      Polynomial.aeval (ptEnd P s) F x = Additive.ofMul (x.toMul ≫ ev F) := by
    refine aeval_eq_of_act (ptEnd P s) (fun F x => Additive.ofMul (x.toMul ≫ ev F)) ?_ ?_ ?_
    · intro x; simp [h1]
    · intro F G x
      rw [hadd, MonObj.comp_mul, ofMul_mul]
    · intro F x
      rw [hX, ← Category.assoc]
      rfl
  have hcard : ∀ j : ℕ, Nat.card {x : Additive (Out.baseOver (Sp K) ⟶ P.A) // l ^ j • x = 0} =
      l ^ (2 * P.g * j) := by
    intro j
    have := (hL.mulN (Sp K) P (l ^ j) (Nat.one_le_pow _ _ hp.pos)).2.2.2.2 K (𝟙 _)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
    rw [mul_comm (2 * P.g) j, pow_mul, ← this]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl)
  obtain ⟨U, hU1, hU2, hU3⟩ := GlobalTheory.T.matrix_polynomial_det_norm_fixed_points l (2 * P.g) _ (ptEnd P s) hcard
  have eq : ∀ F, {x : Additive (Out.baseOver (Sp K) ⟶ P.A) // Polynomial.aeval (ptEnd P s) F x = 0} ≃
      {x : Out.baseOver (Sp K) ⟶ P.A // x ≫ ev F = 1} := fun F =>
    Equiv.subtypeEquiv Additive.toMul fun x => by rw [hact]; exact Iff.rfl
  refine ⟨U, fun F hF => ?_, fun F hF => ?_, fun j pt Mat hb ha => ?_⟩
  · rw [hU1 F (Finite.of_equiv _ (eq F).symm), Nat.card_congr (eq F)]
  · refine (GlobalTheory.PrimePowerTorsion.dense_torsion_and_eq_one hL hL2 K P l hp hl).2 _ fun j x hx => ?_
    have := hU2 F hF j (Additive.ofMul x) hx
    rw [hact] at this
    exact this
  · refine hU3 j (fun i => Additive.ofMul (pt i)) Mat (fun i => hb.pow_eq_one i) (fun y hy => ?_) (fun i => ?_)
    · have := hb.existsUnique (y := y.toMul) hy
      simp only [← linComb_eq]
      exact this
    · rw [← linComb_eq, ← ha.comp_eq i]
      rfl

theorem sq_vol_eq_det : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) (l : ℕ), l.Prime → (l : K) ≠ 0 → M.IsLB → Out.RelAmple P.A M → SymB M → FormIs P M s → ∃ δ : ℕ, Vol P.A.hom M P.g δ ∧ (∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g)) ∧ ∀ (j : ℕ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A)) (Mat : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j))), TorsBasis P.A (l ^ j) pt → ActsBy pt s Mat → (δ : ZMod (l ^ j)) ^ 2 = Mat.det := by
  intro hL hL2 K _ _ P M s l hp hl hM hamp hsym hform
  haveI : Fact l.Prime := ⟨hp⟩
  haveI : IsMonHom s := hform.1
  obtain ⟨δ, -, hvol, hH⟩ := GlobalTheory.sectionsDim_symmetricAmple_pow_eq_mul_pow hL hL2 K P M hM hamp hsym
  refine ⟨δ, hvol, hH, ?_⟩
  obtain ⟨⟨ev, h1, hadd, hX⟩, hev⟩ := GlobalTheory.T.polarisationForm_intPolynomial_bundles hL hL2 K P M s hM hform
  obtain ⟨hmon, hmul, -, hsq, -, hone, hXM⟩ := hev ev h1 hadd hX
  obtain ⟨D, hDp, hDv, hDe⟩ := GlobalTheory.VolPoly.exists_vol_poly hL hL2 K P M s hM hform ev h1 hadd hX
  obtain ⟨U, hU1, hU2, hU3⟩ := exists_matrix hL hL2 P s l hl ev h1 hadd hX
  replace hDp : PolyHom P.g D := hDp
  have hB : ∀ F, (cubeLB P.A ![𝟙 P.A, ev F] P.L).IsLB := fun F => DVR.linComb_isLB _ P.isLB _ _
  have uniq : ∀ F (a : ℝ), Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) →
      Vol P.A.hom (cubeLB P.A ![𝟙 P.A, ev F] P.L) P.g a → (D F : ℝ) = a := fun F a h h' =>
    (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (hB F)).2.1 _ _ (hDv F h) h'
  have fa := fun (ψ : P.A ⟶ P.A) (N : LB P.A.left) (n : ℕ) (hn : 0 < n) (hN : N.IsLB) (hψ : IsFinite ψ.left) =>
    GlobalTheory.relAmple_finite_pow_iso (Sp K) P.A P.A ψ N n hn P.isAb P.isAb hN hψ
  have hid : IsFinite (𝟙 P.A : P.A ⟶ P.A).left := by rw [Over.id_left]; infer_instance

  have hsqr : ∀ F (N : LB P.A.left) (a : ℝ), N.IsLB → Out.RelAmple P.A N → Vol P.A.hom N P.g a →
      LBIso (cubeLB P.A ![𝟙 P.A, ev F] P.L) (lbPow N 2) →
      Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) ∧ (D F : ℝ) = 2 ^ P.g * a := by
    intro F N a hN hA hV hI
    have hN2 : (lbPow N 2).IsLB := DVR.linComb_isLB _ hN _ _
    have hA2 := (fa _ _ 1 one_pos hN2 hid).2.2.2 _ (hB F) hI.symm ((fa _ N 2 two_pos hN hid).2.1.2 hA)
    refine ⟨hA2, uniq F _ hA2 ?_⟩
    have := (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hN).2.2.2.1 2 a one_le_two hV
    exact (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hN2).2.2.1 _ _ (hB F) hI.symm (by simpa using this)
  obtain ⟨hA1, hD1⟩ := hsqr 1 P.L 1 P.isLB P.ample (GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample hL hL2 K P).1 hone
  obtain ⟨-, hDX⟩ := hsqr Polynomial.X M δ hM hamp hvol (hXM hsym)
  replace hD1 : D 1 = 2 ^ P.g := by exact_mod_cast (by simpa using hD1 : (D 1 : ℝ) = 2 ^ P.g)
  replace hDX : D Polynomial.X = 2 ^ P.g * δ := by exact_mod_cast hDX
  have h2 : (2 : ℚ) ^ P.g ≠ 0 := pow_ne_zero _ two_ne_zero

  have hpull : ∀ (G F : Polynomial ℤ) (d : ℕ), IsFinite (ev G).left → MapDeg (ev G).left d →
      Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev F] P.L) →
      Out.RelAmple P.A (cubeLB P.A ![𝟙 P.A, ev (G ^ 2 * F)] P.L) ∧ D (G ^ 2 * F) = d * D F := by
    intro G F d hf hd hA
    have hP : ((cubeLB P.A ![𝟙 P.A, ev F] P.L).pull (ev G).left).IsLB := LB.isLB_pull (hB F) _
    have hA2 := (fa _ _ 1 one_pos hP hid).2.2.2 _ (hB _) (hsq F G).symm ((fa _ _ 1 one_pos (hB F) hf).1 hA)
    refine ⟨hA2, ?_⟩
    have := uniq _ _ hA2 ((GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g hP).2.2.1 _ _ (hB _) (hsq F G).symm
      (GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism K P (ev G) d _ _ (hmon G) hf hd (hB F) hA (hDv F hA)))
    exact_mod_cast this
  have hN : ∀ G, ((D (G ^ 2) / 2 ^ P.g : ℚ) : ℚ_[l]) = ((Polynomial.aeval U G).det : ℤ_[l]) := by
    refine GlobalTheory.PolyNorm.eq_det l (2 * P.g) U (fun G => D (G ^ 2) / 2 ^ P.g) (fun G => IsFinite (ev G).left)
      (hDp.sq.div (2 ^ P.g)) (by simp [hD1]) (fun F => (hDe F).mono fun t h => h.2) ?_ ?_
    · intro F G hF hG
      obtain ⟨-, e, hd⟩ := GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev F) (hmon F) hF
      obtain ⟨-, e', hd'⟩ := GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev G) (hmon G) hG
      obtain ⟨a1, a2⟩ := hpull G 1 _ hG hd' hA1
      have a3 := (hpull F 1 _ hF hd hA1).2
      have a4 := (hpull F _ _ hF hd a1).2
      rw [_root_.mul_one] at a2 a3 a4
      show D ((F * G) ^ 2) / _ = D (F ^ 2) / _ * (D (G ^ 2) / _)
      rw [mul_pow, a4, a3, hD1]
      field_simp
    · intro F hF
      obtain ⟨hfin, e, hd⟩ := GlobalTheory.T.mapDegree_eq_expChar_pow_mul_card_kernel K P (ev F) (hmon F) hF
      have a3 := (hpull F 1 _ hF hd hA1).2
      rw [_root_.mul_one] at a3
      show ‖((D (F ^ 2) / _ : ℚ) : ℚ_[l])‖ = _
      rw [a3, hD1, mul_div_assoc, div_self h2, _root_.mul_one, hU1 F hfin]
      have hc : ‖((ringExpChar K : ℕ) : ℚ_[l])‖ = 1 := by
        rw [Padic.norm_natCast_eq_one_iff]
        rcases expChar_is_prime_or_one K (ringExpChar K) with h | h
        · rw [Nat.coprime_primes hp h]
          rintro rfl'
          obtain ⟨q, hq⟩ := ExpChar.exists K
          have e1 : ringExpChar K = q := ringExpChar.eq K q
          cases hq with
          | zero => rw [e1] at h; exact Nat.not_prime_one h
          | prime hq => exact hl (by rw [rfl', e1]; exact CharP.cast_eq_zero K q)
        · rw [h]; exact Nat.coprime_one_right l
      push_cast
      rw [norm_mul, norm_pow, hc, one_pow, _root_.one_mul]
  have hH0 : ∀ F H, Polynomial.aeval U H = 0 → D (F + H) / 2 ^ P.g = D F / 2 ^ P.g := by
    intro F H h
    congr 1
    refine hDp.eq_of_eventually _ _ ((hDe F).mono fun t ht => ?_)
    have e : ev (F + H + t) = ev (F + t) := by
      rw [add_right_comm, hadd (F + t) H, hU2 H h, _root_.mul_one]
    have := uniq (F + H + t) (D (F + t)) (by rw [e]; exact ht.1) (by rw [e]; exact hDv _ ht.1)
    exact_mod_cast this
  have key := GlobalTheory.sq_eq_det_aeval_of_sq l (2 * P.g) P.g U (fun F => D F / 2 ^ P.g) (hDp.div (2 ^ P.g)) hN hH0
    Polynomial.X
  rw [hDX, mul_div_cancel_left₀ _ h2, Polynomial.aeval_X] at key
  have key' : (δ : ℤ_[l]) ^ 2 = U.det := by
    apply Subtype.ext
    rw [← key]
    push_cast
    rfl
  intro j pt Mat hb ha
  rw [← hU3 j pt Mat hb ha, ← key']
  simp

end GlobalTheory.SectionCount
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_count_sq_eq_det_form_on_torsion : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (s : P.A ⟶ P.A) (l : ℕ), l.Prime → (l : K) ≠ 0 → M.IsLB → Out.RelAmple P.A M → SymB M → FormIs P M s → ∃ δ : ℕ, Vol P.A.hom M P.g δ ∧ (∀ e ≥ 1, SectionsHaveFiniteDimension P.A.hom (lbPow M e) (δ * e ^ P.g)) ∧ ∀ (j : ℕ) (pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A)) (Mat : Matrix (Fin (2 * P.g)) (Fin (2 * P.g)) (ZMod (l ^ j))), TorsBasis P.A (l ^ j) pt → ActsBy pt s Mat → (δ : ZMod (l ^ j)) ^ 2 = Mat.det := by
  atlas_forward_decl GlobalTheory.SectionCount.sq_vol_eq_det
end
