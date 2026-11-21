import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.RationalPointsDense
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.ClassFiniteOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.IsIntegralOfIntOE
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HermLatFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.PosDefOfDefiniteSignatureHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictInter

section
noncomputable section

open Matrix NumberField
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.HermLatFin

variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)

theorem herm_add_left (x x' y : Fin M → E) : herm σ J (x + x') y = herm σ J x y + herm σ J x' y := by
  simp only [herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem herm_add_right (x y y' : Fin M → E) : herm σ J x (y + y') = herm σ J x y + herm σ J x y' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (a : E) (x y : Fin M → E) : herm σ J (a • x) y = σ a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_smul_right (a : E) (x y : Fin M → E) : herm σ J x (a • y) = a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_zero_left (y : Fin M → E) : herm σ J 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin M → E) : herm σ J x 0 = 0 := by
  simp [herm]

theorem herm_scale (D : E) (x y : Fin M → E) : herm σ (D • J) x y = D * herm σ J x y := by
  simp only [herm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_single_left (i : Fin M) (k : ℕ) (y : Fin M → E) :
    herm σ J (Pi.single i (k : E)) y = (k : E) * (J.mulVec y) i := by
  classical
  simp only [herm]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

variable [NumberField E]

theorem fg_of_den (N : Submodule (𝓞 E) (Fin M → E)) (d : ℕ) (hd : 0 < d)
    (h : ∀ y ∈ N, ∀ j, IsIntegral ℤ ((d : E) * y j)) : N.FG := by
  classical

  let f : (Fin M → 𝓞 E) →ₗ[𝓞 E] (Fin M → E) :=
    LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  let sc : (Fin M → E) →ₗ[𝓞 E] (Fin M → E) := (d : 𝓞 E) • LinearMap.id
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hsc : ∀ y : Fin M → E, ∀ j, sc y j = (d : E) * y j := by
    intro y j
    simp [sc, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hinj : Function.Injective sc := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    rw [hsc, hsc] at this
    exact mul_left_cancel₀ hd' this
  have hle : N.map sc ≤ LinearMap.range f := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun j => ⟨(d : E) * y j, h y hy j⟩, ?_⟩
    funext j
    rw [hsc]
    rfl
  have hfg : (N.map sc).FG := by
    rw [← Submodule.map_comap_eq_of_le hle]
    exact (IsNoetherian.noetherian _).map f
  exact Submodule.fg_of_fg_map_injective sc hinj hfg

theorem sub_finite (N : Submodule (𝓞 E) (Fin M → E)) (hN : N.FG) (n : ℕ) (hn : 0 < n) :
    {s : Set (Fin M → E) | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
      (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N}.Finite := by
  classical
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := N)

  let rep : (S → Fin n) → (Fin M → E) := fun c => ∑ g : S, ((c g : ℕ) : ℤ) • ((g : N) : Fin M → E)
  let T : Set (Fin M → E) := Set.range rep
  have hT : T.Finite := Set.finite_range rep
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hdec : ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x = t + (n : E) • z := by
    intro x hx
    have hmem : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (S : Set N) := by rw [hS]; trivial
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hmem
    have hx' : x = ∑ g ∈ S, a g • ((g : N) : Fin M → E) := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    let c : S → Fin n := fun g => ⟨(a g % n).toNat, by
      have h1 := Int.emod_nonneg (a g) hnZ.ne'
      have h2 := Int.emod_lt_of_pos (a g) hnZ
      omega⟩
    refine ⟨rep c, ⟨c, rfl⟩, ∑ g ∈ S, (a g / n) • ((g : N) : Fin M → E), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ g.2
    · have hc : ∀ g : S, (((c g : ℕ) : ℤ)) = a g % n := fun g => by
        simp only [c]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne')
      simp only [rep, hc]
      rw [Finset.sum_coe_sort S (fun g => (a g % (n : ℤ)) • ((g : N) : Fin M → E)), hx',
        Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Int.cast_smul_eq_zsmul E, smul_comm ((n : E)) _ _, ← Int.cast_smul_eq_zsmul E (a g / n),
        smul_smul, ← Int.cast_smul_eq_zsmul E (a g % n), ← add_smul]
      congr 1
      have h2 : ((a g : ℤ) : E) = ((a g % n : ℤ) : E) + (n : E) * ((a g / n : ℤ) : E) := by
        have hdm : a g % (n : ℤ) + (n : ℤ) * (a g / n) = a g := by
          first
            | exact Int.emod_add_ediv _ _
            | exact Int.emod_add_ediv' _ _
            | (rw [Int.emod_def]; ring)
            | exact EuclideanDomain.mod_add_div _ _
        have := congrArg (fun q : ℤ => (q : E)) hdm
        push_cast at this
        rw [this]
      rw [h2]
      ring

  have key : ∀ s s' : Set (Fin M → E), s ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s' ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s ∩ T = s' ∩ T → s ⊆ s' := by
    rintro s s' ⟨⟨G, hG⟩, hns, hsN⟩ ⟨⟨G', hG'⟩, hns', -⟩ heq x hx
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x (hsN hx)
    rw [← hG] at hx hns
    rw [← hG'] at hns' ⊢
    have hts : t ∈ G := by
      have := G.sub_mem hx (hns z hz)
      simpa using this
    have hts' : t ∈ s' ∩ T := heq ▸ ⟨(show t ∈ s by rw [← hG]; exact hts), ht⟩
    rw [← hG'] at hts'
    exact G'.add_mem hts'.1 (hns' z hz)
  refine Set.Finite.of_finite_image (f := fun s => s ∩ T) ?_ ?_
  · refine (hT.finite_subsets).subset ?_
    rintro _ ⟨s, -, rfl⟩
    exact Set.inter_subset_right
  · intro s hs s' hs' heq
    exact Set.Subset.antisymm (key s s' hs hs' heq) (key s' s hs' hs heq.symm)

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

section
noncomputable section

open Matrix NumberField
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.HermLatFin

variable {E : Type} [Field E] [NumberField E]

theorem int_nat (m : ℕ) : IsIntegral ℤ (m : E) := by
  have h := isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ))
  simpa using h

theorem int_sigma (σ : E →+* E) {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (σ a) := ha.map σ.toIntAlgHom

theorem mat_den {M : ℕ} (A : Matrix (Fin M) (Fin M) E) : ∃ d : ℕ, 0 < d ∧ ∀ i j, IsIntegral ℤ ((d : E) * A i j) := by
  have hex : ∀ a : E, ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
    intro a
    have halg : IsAlgebraic ℤ a := by
      first
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact (IsFractionRing.isAlgebraic_iff (R := ℤ) (K := ℚ)).mpr (Algebra.IsAlgebraic.isAlgebraic a)
      | exact Algebra.IsAlgebraic.isAlgebraic a
    obtain ⟨y, hy0, hy⟩ : ∃ y ≠ (0 : ℤ), IsIntegral ℤ (y • a) := by
      first
      | exact halg.exists_integral_multiple
      | exact exists_integral_multiple halg
    refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
    have hcast : ((y.natAbs : ℕ) : E) = (((y.natAbs : ℕ) : ℤ) : E) := (Int.cast_natCast _).symm
    rcases (show ((y.natAbs : ℕ) : ℤ) = y ∨ ((y.natAbs : ℕ) : ℤ) = -y by omega) with h | h
    · rw [hcast, h, ← zsmul_eq_mul]
      exact hy
    · rw [hcast, h, Int.cast_neg, neg_mul, ← zsmul_eq_mul]
      exact hy.neg
  choose d hd0 hd using fun p : Fin M × Fin M => hex (A p.1 p.2)
  refine ⟨∏ p, d p, Finset.prod_pos fun p _ => hd0 p, fun i j => ?_⟩
  have hsplit : (∏ p, d p : ℕ) = (∏ p ∈ Finset.univ.erase (i, j), d p) * d (i, j) :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
  rw [hsplit, Nat.cast_mul, mul_assoc]
  exact (int_nat _).mul (hd (i, j))

theorem lattice_classes_finite_refinement : LatFin := by
  intro E _ _ σ M J D T c0 hσ hpos hD hT hc0
  classical
  set J' : Matrix (Fin M) (Fin M) E := (D : E) • J with hJ'
  have hpos' : ∀ τ : E →+* ℂ, (J'.map τ).PosDef := by
    intro τ
    have : J'.map τ = (D : ℂ) • J.map τ := by
      ext i j
      simp [hJ', map_natCast]
    rw [this]
    exact (hpos τ).smul (by exact_mod_cast hD)
  obtain ⟨SE, hSEf, hSE⟩ := hermitian_lattice_finite E M σ J' T hσ hpos' hT
  let Sub : Submodule (𝓞 E) (Fin M → E) → Set (Set (Fin M → E)) := fun N₀ =>
    {s | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧ (∀ x ∈ N₀, (c0 : E) • x ∈ s) ∧ s ⊆ N₀}
  refine ⟨⋃ N₀ ∈ {N₀ | N₀ ∈ SE ∧ N₀.FG}, Sub N₀,
    Set.Finite.biUnion (hSEf.subset fun N₀ h => h.1) fun N₀ h => sub_finite N₀ h.2 c0 hc0, ?_⟩
  intro Λ h1 h2 h3 h4
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'

  have hJdet : J.det ≠ 0 := by
    intro h0
    obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hpos τ).isUnit
    have e : (J.map τ).det = τ J.det := (RingHom.map_det τ J).symm
    rw [e, h0, map_zero] at hu
    exact not_isUnit_zero hu
  obtain ⟨d, hd, hdJ⟩ := mat_den J⁻¹
  set N : Submodule (𝓞 E) (Fin M → E) := Submodule.span (𝓞 E) (Λ : Set (Fin M → E)) with hNdef
  have smul_coe : ∀ (a : 𝓞 E) (y : Fin M → E), a • y = (a : E) • y := fun a y => rfl

  have hI1 : ∀ x ∈ Λ, ∀ y ∈ N, IsIntegral ℤ ((D : E) * herm σ J x y) := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h3 x hx y hy
    | zero => rw [herm_zero_right, mul_zero]; exact isIntegral_zero
    | add y z _ _ h1 h2 => rw [herm_add_right, mul_add]; exact h1.add h2
    | smul a y _ h1 =>
      rw [smul_coe, herm_smul_right, mul_left_comm]
      exact a.isIntegral_coe.mul h1
  have hI : ∀ x ∈ N, ∀ y ∈ N, IsIntegral ℤ (herm σ J' x y) := by
    intro x hx y hy
    rw [hJ', herm_scale]
    induction hx using Submodule.span_induction with
    | mem x hx => exact hI1 x hx y hy
    | zero => rw [herm_zero_left, mul_zero]; exact isIntegral_zero
    | add x z _ _ h1 h2 => rw [herm_add_left, mul_add]; exact h1.add h2
    | smul a x _ h1 =>
      rw [smul_coe, herm_smul_left, mul_left_comm]
      exact (int_sigma σ a.isIntegral_coe).mul h1

  have hDual : ∀ y : Fin M → E, (∀ x ∈ N, IsIntegral ℤ (herm σ J' x y)) → (T : E) • y ∈ N := by
    intro y hy
    refine Submodule.subset_span (h4 y fun x hx => ?_)
    have := hy x (Submodule.subset_span hx)
    rwa [hJ', herm_scale] at this

  obtain ⟨k, hk, hkΛ⟩ := h2
  have hsing : ∀ i, (Pi.single i (k : E) : Fin M → E) ∈ Λ := by
    intro i
    have := hkΛ i 1 isIntegral_one
    rwa [mul_one] at this
  have hNfg : N.FG := by
    refine fg_of_den N (d * D * k) (Nat.mul_pos (Nat.mul_pos hd hD) hk) fun y hy j => ?_
    have hJy : ∀ i, IsIntegral ℤ ((D : E) * (k : E) * (J.mulVec y) i) := by
      intro i
      have := hI1 _ (hsing i) y hy
      rwa [herm_single_left, ← mul_assoc] at this
    obtain ⟨w, hw⟩ : ∃ w, w = J.mulVec y := ⟨_, rfl⟩
    have hy' : y = J⁻¹.mulVec w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (Ne.isUnit hJdet), Matrix.one_mulVec]
    rw [← hw] at hJy
    have : ((d * D * k : ℕ) : E) * y j = ∑ i, ((d : E) * J⁻¹ j i) * ((D : E) * (k : E) * w i) := by
      conv_lhs => rw [hy']
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [this]
    exact IsIntegral.sum _ fun i _ => (hdJ j i).mul (hJy i)
  have hNspan : Submodule.span E (N : Set (Fin M → E)) = ⊤ := by
    refine eq_top_iff.2 fun v _ => ?_
    have hkE : (k : E) ≠ 0 := by exact_mod_cast hk.ne'
    have hv : v = ∑ j, (v j / (k : E)) • (Pi.single j (k : E) : Fin M → E) := by
      conv_lhs => rw [← Finset.univ_sum_single v]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Pi.single_smul]
      congr 1
      rw [smul_eq_mul, div_mul_cancel₀ _ hkE]
    rw [hv]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span (hsing j)))
  have hAdm : admitted σ J' T N := ⟨⟨hNfg, hNspan⟩, hI, hDual⟩
  obtain ⟨N₀, hN₀, g, hg, hgN⟩ := hSE N hAdm

  have hJ'det : J'.det ≠ 0 := by
    rw [hJ', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hDE) hJdet
  have hgdet : g.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact hJ'det this.symm
  have hgU : PI.UJClassFin.cT σ g * J * g = J := by
    have e1 : (g.map σ)ᵀ * J' * g = (D : E) • (PI.UJClassFin.cT σ g * J * g) := by
      rw [hJ', Matrix.mul_smul, Matrix.smul_mul]
      rfl
    have := hg
    unfold IsUJ at this
    rw [e1] at this
    exact smul_right_injective _ hDE this
  let G : GL (Fin M) E := Matrix.nonsingInvUnit g (Ne.isUnit hgdet)
  have hGg : ((G : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = g := rfl
  have hGU : G ∈ PI.UJClassFin.UJ σ J := by
    show PI.UJClassFin.cT σ (G : Matrix (Fin M) (Fin M) E) * J * (G : Matrix (Fin M) (Fin M) E) = J
    rw [hGg]; exact hgU
  have hgi : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ (Ne.isUnit hgdet)
  have hig : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ (Ne.isUnit hgdet)

  have hN₀eq : (N₀ : Set (Fin M → E)) = (fun x => g⁻¹.mulVec x) '' (N : Set (Fin M → E)) := by
    rw [← hgN, Set.image_image]
    simp only [Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec, Set.image_id']
  have hN₀fg : N₀.FG := by
    have : N₀ = N.map ((Matrix.mulVecLin g⁻¹).restrictScalars (𝓞 E)) := by
      apply SetLike.coe_injective
      rw [hN₀eq, Submodule.map_coe]
      rfl
    rw [this]
    exact hNfg.map _

  have hc0N : ∀ y ∈ N, (c0 : E) • y ∈ Λ := by
    let Nc : Submodule (𝓞 E) (Fin M → E) :=
      { carrier := {y | ∀ a : 𝓞 E, (c0 : E) • ((a : E) • y) ∈ Λ}
        add_mem' := fun {y z} hy hz a => by rw [smul_add, smul_add]; exact Λ.add_mem (hy a) (hz a)
        zero_mem' := fun a => by rw [smul_zero, smul_zero]; exact Λ.zero_mem
        smul_mem' := fun b y hy a => by
          show (c0 : E) • ((a : E) • (b • y)) ∈ Λ
          have e : (a : E) • (b • y) = ((a * b : 𝓞 E) : E) • y := by
            rw [smul_coe b y, smul_smul]
            rfl
          rw [e]
          exact hy (a * b) }
    have hle : N ≤ Nc := by
      rw [hNdef, Submodule.span_le]
      intro x hx a
      rw [smul_smul]
      exact h1 x hx _ a.isIntegral_coe
    intro y hy
    have := hle hy 1
    rwa [show ((1 : 𝓞 E) : E) = 1 from rfl, one_smul] at this
  let s : Set (Fin M → E) := (fun x => g⁻¹.mulVec x) '' (Λ : Set (Fin M → E))
  have hs : s ∈ Sub N₀ := by
    refine ⟨⟨Λ.map (Matrix.mulVecLin g⁻¹).toAddMonoidHom, by rw [AddSubgroup.coe_map]; rfl⟩, ?_, ?_⟩
    · intro x hx
      have hgx : g.mulVec x ∈ N := by rw [← SetLike.mem_coe, ← hgN]; exact ⟨x, hx, rfl⟩
      refine ⟨(c0 : E) • g.mulVec x, hc0N _ hgx, ?_⟩
      show g⁻¹.mulVec ((c0 : E) • g.mulVec x) = (c0 : E) • x
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hgi, Matrix.one_mulVec]
    · rintro _ ⟨x, hx, rfl⟩
      show g⁻¹.mulVec x ∈ (N₀ : Set (Fin M → E))
      rw [hN₀eq]
      exact Set.mem_image_of_mem _ (Submodule.subset_span hx)
  refine ⟨s, Set.mem_biUnion ⟨hN₀, hN₀fg⟩ hs, ⟨G, hGU⟩, ?_⟩
  show (Λ : Set (Fin M → E)) = (fun x => g.mulVec x) '' s
  rw [Set.image_image]
  simp only [Matrix.mulVec_mulVec, hig, Matrix.one_mulVec, Set.image_id']

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

section
noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incl_mem_Oh {e : E} (he : IsIntegral ℤ e) : inclR (Af F) e ∈ Oh F E :=
  tmul_mem_Oh intAf_one he

theorem one_mem_Oh : (1 : Af F ⊗[F] E) ∈ Oh F E := by
  rw [Algebra.TensorProduct.one_def]
  exact tmul_mem_Oh intAf_one isIntegral_one

theorem oh_inter {e : E} (he : inclR (Af F) e ∈ Oh F E) : IsIntegral ℤ e := by
  let ψ : Af F ⊗[F] E →+* E ⊗[F] Af F := (Algebra.TensorProduct.comm F (Af F) E).toRingHom
  have hψ : ∀ z ∈ Oh F E, ψ z ∈ Formalism.MainNotions.S.IntAf F E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, e', he', rfl⟩ := hz
      have e1 : ψ (a ⊗ₜ[F] e') = (e' ⊗ₜ[F] (1 : Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [e1]
      refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨e', ⟨⟨e', he'⟩, rfl⟩⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | add x y _ _ h1 h2 => rw [map_add]; exact Subring.add_mem _ h1 h2
    | neg x _ h1 => rw [map_neg]; exact Subring.neg_mem _ h1
  have e2 : ψ (inclR (Af F) e) = Formalism.UG.inclE (F := F) (Af F) e := rfl
  have := PIW.AdelClassFin.dual_intersection F E e (e2 ▸ hψ _ he)
  obtain ⟨b, hb⟩ := this
  rw [← hb]
  exact b.isIntegral_coe

theorem up_nat {M : ℕ} (L : Set (Fin M → E))
    (h4 : ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) :
    ∃ u : ℕ, 0 < u ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i) := by
  obtain ⟨c, hc, hL⟩ := h4
  obtain ⟨u, hu, c', huc⟩ := nat_mult c hc
  refine ⟨u, hu, fun x hx i => ?_⟩
  have : (u : F) • x i = (c' : F) • ((c : F) • x i) := by
    rw [smul_smul]
    congr 1
    have := congrArg (algebraMap (𝓞 F) F) huc
    rw [map_natCast, map_mul] at this
    rw [this, mul_comm]
  rw [this, Algebra.smul_def]
  exact (IsIntegral.algebraMap (c'.isIntegral_coe)).mul (hL x hx i)

variable {M : ℕ}

theorem up_Oh (L : Set (Fin M → E)) {u : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    {w : Fin M → Af F ⊗[F] E} (hw : w ∈ latHat F E L) (i : Fin M) : u • w i ∈ Oh F E := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    show u • (a ⊗ₜ[F] x i) ∈ Oh F E
    rw [nsmul_tmul_F]
    exact tmul_mem_Oh ha (hu x hx i)
  | zero => show u • (0 : Af F ⊗[F] E) ∈ Oh F E; rw [smul_zero]; exact zero_mem _
  | add w w' _ _ h1 h2 => show u • (w i + w' i) ∈ Oh F E; rw [smul_add]; exact add_mem h1 h2
  | neg w _ h1 => show u • (-w i) ∈ Oh F E; rw [smul_neg]; exact neg_mem h1

theorem low_vec (L : Set (Fin M → E)) {k : ℕ}
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    {w : Fin M → Af F ⊗[F] E} (hw : ∀ i, w i ∈ Oh F E) : k • w ∈ latHat F E L := by
  rw [← Finset.univ_sum_single (k • w)]
  exact AddSubgroup.sum_mem _ fun i _ => single_mem L hk (hw i) i

theorem den_mat (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :
    ∃ m : ℕ, 0 < m ∧ ∀ l j, m • g l j ∈ Oh F E := by
  classical
  choose mf hmf hmO using fun p : Fin M × Fin M => den (g p.1 p.2)
  refine ⟨∏ p, mf p, Finset.prod_pos (fun p _ => hmf p), fun l j => ?_⟩
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ (l, j))
  rw [hq, mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hmO (l, j)) _

variable (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E)

theorem sigR_Oh {z : Af F ⊗[F] E} (hz : z ∈ Oh F E) : sigR (Af F) σ z ∈ Oh F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, e, he, rfl⟩ := hz
    have e1 : sigR (Af F) σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := by simp [sigR]
    rw [e1]
    exact tmul_mem_Oh ha (by simpa using int_sigma (σ : E →+* E) he)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [map_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [map_neg]; exact neg_mem h1

def hermA (X Y : Fin M → Af F ⊗[F] E) : Af F ⊗[F] E :=
  dotProduct (fun i => sigR (Af F) σ (X i)) ((JR (Af F) J).mulVec Y)

theorem hermA_vinc (x y : Fin M → E) :
    hermA σ J (vinc (F := F) x) (vinc y) = inclR (Af F) (PI.HermLatFin.herm (σ : E →+* E) J x y) := by
  simp only [hermA, dotProduct, Matrix.mulVec, vinc, JR, Matrix.map_apply, sigR_inclR, PI.HermLatFin.herm,
    map_sum, map_mul, Finset.mul_sum, AlgHom.coe_toRingHom]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermA_add_left (X X' Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (X + X') Y = hermA σ J X Y + hermA σ J X' Y := by
  simp only [hermA, dotProduct, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermA_neg_left (X Y : Fin M → Af F ⊗[F] E) : hermA σ J (-X) Y = -hermA σ J X Y := by
  simp only [hermA, dotProduct, Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem hermA_zero_left (Y : Fin M → Af F ⊗[F] E) : hermA σ J 0 Y = 0 := by
  simp [hermA, dotProduct]

theorem hermA_smul_left (c : Af F ⊗[F] E) (X Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (c • X) Y = sigR (Af F) σ c * hermA σ J X Y := by
  simp only [hermA, dotProduct, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem hermA_single_left (i : Fin M) (p : Af F ⊗[F] E) (Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (Pi.single i p) Y = sigR (Af F) σ p * ((JR (Af F) J).mulVec Y) i := by
  rw [hermA, dotProduct, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

theorem hermA_unitary (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hg : cT (sigR (Af F) σ) g * JR (Af F) J * g = JR (Af F) J) (X Y : Fin M → Af F ⊗[F] E) :
    hermA σ J (g.mulVec X) (g.mulVec Y) = hermA σ J X Y := by
  have h1 : (fun i => sigR (Af F) σ ((g.mulVec X) i)) =
      (g.map (sigR (Af F) σ)).mulVec (fun i => sigR (Af F) σ (X i)) := by
    funext i
    exact RingHom.map_mulVec _ g X i
  have e : (g.map (sigR (Af F) σ))ᵀ * (JR (Af F) J * g) = JR (Af F) J := by
    rw [← Matrix.mul_assoc]; exact hg
  unfold hermA
  rw [h1, ← Matrix.vecMul_transpose (g.map (sigR (Af F) σ)), ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, e]

theorem finMat_unitary (h : HA (AF F) σ J) :
    cT (sigR (Af F) σ) (finMat σ J h) * JR (Af F) J * finMat σ J h = JR (Af F) J := by
  have hm : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *
      JR (AF F) J * ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  let φ := Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)
  have hφs : ∀ z, φ (sigR (AF F) σ z) = sigR (Af F) σ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [φ, sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hφJ : (JR (AF F) J).map φ = JR (Af F) J := by
    ext i j
    simp [φ, JR, inclR, Algebra.TensorProduct.map_tmul]
  have hcT : ∀ X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      (cT (sigR (AF F) σ) X).map φ = cT (sigR (Af F) σ) (X.map φ) := by
    intro X
    ext i j
    simp [cT, hφs]
  have := congrArg (fun X => X.map φ) hm
  simp only [mapAlg_mul, hcT, hφJ] at this
  exact this

theorem hermA_Oh {u dJ : ℕ} (hJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j)) {X Y : Fin M → Af F ⊗[F] E}
    (hX : ∀ i, u • X i ∈ Oh F E) (hY : ∀ i, u • Y i ∈ Oh F E) :
    (u * u * dJ) • hermA σ J X Y ∈ Oh F E := by
  have : (u * u * dJ) • hermA σ J X Y = ∑ i, ∑ j,
      sigR (Af F) σ (u • X i) * (inclR (Af F) ((dJ : E) * J i j) * (u • Y j)) := by
    simp only [hermA, dotProduct, Matrix.mulVec, JR, Matrix.map_apply, Finset.mul_sum, Finset.smul_sum,
      map_nsmul, map_mul, map_natCast, nsmul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [this]
  exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ =>
    Oh_mul (sigR_Oh σ (hX i)) (Oh_mul (incl_mem_Oh (hJ i j)) (hY j))

end PI.UnitaryGroupMassFormula.UJClassFin
end
end
