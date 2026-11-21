import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.HeckeDoubleCosets.PHeckeFormal

section
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section

variable {G K : Type} [Group G] [Group K]

theorem mem_Gq {ρ : G →* K} {q : K} {δ : G} : δ ∈ Gq ρ q ↔ ∃ γ, q⁻¹ * ρ γ * q = ρ δ := by
  unfold Gq
  simp [MulAut.conj_apply]

theorem F_rep {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (hF : Inv ρ F) (a b : G)
    (h : b * a⁻¹ ∈ Gq ρ q) (y : Fin (m + 1) → K) :
    F (fun j => q * ρ b * y j) = F (fun j => q * ρ a * y j) := by
  obtain ⟨γ, hγ⟩ := mem_Gq.mp h
  have hρ : ρ γ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by
    rw [map_mul, map_inv] at hγ
    calc ρ γ = q * (q⁻¹ * ρ γ * q) * q⁻¹ := by group
      _ = q * ρ b * (ρ a)⁻¹ * q⁻¹ := by rw [hγ]; group
  have key : (fun j => q * ρ b * y j) = fun j => ρ γ • (q * ρ a * y j) := by
    funext j
    rw [smul_eq_mul, hρ]
    group
  rw [key]
  exact hF γ _

theorem rel_out_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) :
    (c.out * g) * (Quotient.mk'' (c.out * g) : Quotient (QuotientGroup.rightRel s)).out⁻¹ ∈ s := by
  have hx := Quotient.mk_out (s := QuotientGroup.rightRel s) (c.out * g)
  exact QuotientGroup.rightRel_apply.mp hx

def actQ (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g : G) : Quotient (QuotientGroup.rightRel s) :=
  Quotient.mk'' (c.out * g)

theorem actQ_one (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) : actQ s c 1 = c := by
  simp [actQ]

theorem actQ_mul (s : Subgroup G) (c : Quotient (QuotientGroup.rightRel s)) (g h : G) :
    actQ s c (g * h) = actQ s (actQ s c g) h := by
  unfold actQ
  apply Quotient.sound'
  apply QuotientGroup.rightRel_apply.mpr
  convert s.inv_mem (rel_out_mul s c g) using 1
  group

theorem actQ_bij (s : Subgroup G) (g : G) : Function.Bijective fun c => actQ s c g := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun c => actQ s c g⁻¹, fun c => ?_, fun c => ?_⟩
  · show actQ s (actQ s c g) g⁻¹ = c
    rw [← actQ_mul, mul_inv_cancel, actQ_one]
  · show actQ s (actQ s c g⁻¹) g = c
    rw [← actQ_mul, inv_mul_cancel, actQ_one]

theorem hecke_apply {m : ℕ} (ρ : G →* K) (q : K) (F : (Fin (m + 1) → K) → ℝ) (y : Fin (m + 1) → K) :
    hecke ρ (MonoidHom.id K) q F y =
      ((Gq ρ q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), F (fun j => q * ρ c.out * y j) :=
  rfl

end

theorem pHeckeFormal : PHeckeFormal := by
  intro G K _ _ ρ q hfin m F F' c hF
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  refine ⟨?_, ?_, ?_⟩
  · intro g y
    rw [hecke_apply, hecke_apply]
    congr 1
    refine Eq.trans ?_ (finsum_comp_equiv (Equiv.ofBijective _ (actQ_bij (Gq ρ q) g)))
    apply finsum_congr
    intro c'
    simp only [Equiv.ofBijective_apply]
    rw [← F_rep ρ q F hF (actQ (Gq ρ q) c' g).out (c'.out * g) (rel_out_mul _ c' g) y]
    congr 1
    funext j
    rw [smul_eq_mul, map_mul]
    group
  · funext y
    rw [hecke_apply]
    unfold dC
    simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  · funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hecke_apply, finsum_eq_sum_of_fintype,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    ring

theorem bd_cmap {G H : Type} [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Chn G (m + 1)) :
    bd H m (cmap f (m + 1) z) = cmap f m (bd G m z) := by
  have hc : ∀ (j : Fin (m + 1)) (g : Fin (m + 1) → G),
      (fun i => f (Fin.contractNth j (· * ·) g i)) = Fin.contractNth j (· * ·) (fun i => f (g i)) :=
    fun j g => Fin.comp_contractNth _ _ (map_mul f) j g
  have key : (bd H m).comp (cmap f (m + 1)) = (cmap f m).comp (bd G m) := by
    apply Finsupp.lhom_ext
    intro g r
    simp [bd, cmap, Finsupp.mapDomain_single, map_sum, Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hc]
    rw [Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single, hc]
  exact LinearMap.congr_fun key z

theorem pHeckeKer (hT : PTransfer) (hE : PEvDC) : PHeckeKer := by
  intro hSEv G K _ _ ρ hρ q hfin m F hF hdF hcyc z hz
  haveI := Fintype.ofFinite (Quotient (QuotientGroup.rightRel (Gq ρ q)))
  have heq : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q))) (g : G) (y : Fin (m + 2) → G),
      ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ (actQ (Gq ρ q) c g).out * ρ (y j)) =
        ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (g * y j)) := by
    intro c g y
    have e := F_rep ρ q F hF (actQ (Gq ρ q) c g).out (c.out * g) (rel_out_mul _ c g) (fun j => ρ (y j))
    rw [← e]
    congr 1
    congr 1
    funext j
    rw [map_mul, map_mul]
    group
  have hcoc : ∀ c : Quotient (QuotientGroup.rightRel (Gq ρ q)),
      dC (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) = 0 := by
    intro c
    funext y
    have h := congrFun hdF (fun j => q * ρ c.out * ρ (y j))
    unfold dC at h ⊢
    simp only [Pi.zero_apply] at h ⊢
    rw [← mul_zero (((Gq ρ q).index : ℝ)⁻¹), ← h, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hpp : ∀ {S T : Type} [Group S] [Group T] (φ : S →* T) {n : ℕ} (g : Fin n → S) (j : Fin (n + 1)),
      Fin.partialProd (fun i => φ (g i)) j = φ (Fin.partialProd g j) := by
    intro S T _ _ φ n g j
    refine Fin.inductionOn j ?_ ?_
    · simp
    · intro j ih
      rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]
  have hstab : ∀ (c : Quotient (QuotientGroup.rightRel (Gq ρ q)))
      (w : Chn (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) (m + 1)), IsCyc w →
      ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w = 0 := by
    intro c w hw
    have hmem : ∀ h : stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c,
        q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ ∈ ρ.range := by
      intro h
      have h1 : actQ (Gq ρ q) c h = c := h.2
      have h3 : (Quotient.mk'' (c.out * (h : G)) : Quotient (QuotientGroup.rightRel (Gq ρ q))) =
          Quotient.mk'' c.out := by
        rw [Quotient.out_eq']
        exact h1
      have h2 : c.out * (c.out * (h : G))⁻¹ ∈ Gq ρ q := QuotientGroup.rightRel_apply.mp (Quotient.exact' h3)
      obtain ⟨γ, hγ⟩ := mem_Gq.mp h2
      refine ⟨γ⁻¹, ?_⟩
      rw [map_inv]
      rw [map_mul, map_inv, map_mul] at hγ
      calc (ρ γ)⁻¹ = (q * (q⁻¹ * ρ γ * q) * q⁻¹)⁻¹ := by group
        _ = _ := by rw [hγ]; group
    let ψ : (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c) →* K :=
      (MulAut.conj (q * ρ c.out)).toMonoidHom.comp (ρ.comp (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype)
    have hψ : ∀ h, ψ h ∈ ρ.range := fun h => by
      convert hmem h using 1
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
      done
    let φ := (MonoidHom.ofInjective hρ).symm.toMonoidHom.comp (ψ.codRestrict ρ.range hψ)
    have hφ : ∀ h, ρ (φ h) = q * ρ c.out * ρ h * (q * ρ c.out)⁻¹ := by
      intro h
      rw [← MonoidHom.ofInjective_apply hρ (x := φ h)]
      simp [φ, ψ, MulAut.conj_apply]
      group
    have hz' : IsCyc (cmap φ (m + 1) w) := by
      unfold IsCyc at hw ⊢
      rw [bd_cmap, hw, map_zero]
    have hsev := (hSEv G K K ρ m F hF hdF).2 (q * ρ c.out) 1 _ hz'
    have hcalc : ev (stabR (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) c).subtype
        (fun y : Fin (m + 2) → G => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) 1 w =
        ((Gq ρ q).index : ℝ)⁻¹ * ev ρ F (q * ρ c.out) (cmap φ (m + 1) w) := by
      unfold ev cmap
      rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (by intro b; simp) (by intro b r1 r2; ring),
        Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro g _
      simp only [hpp, hφ, smul_eq_mul, Subgroup.coe_subtype, mul_one, inv_mul_cancel_right]
      ring
    rw [hcalc, hsev, hcyc _ hz', mul_zero]
  have hfinal := hT G (Quotient (QuotientGroup.rightRel (Gq ρ q))) (actQ (Gq ρ q)) (actQ_one _) (actQ_mul _) m
    (fun c y => ((Gq ρ q).index : ℝ)⁻¹ * F (fun j => q * ρ c.out * ρ (y j))) heq hcoc hstab z hz
  refine Eq.trans ?_ hfinal
  unfold ev
  apply Finsupp.sum_congr
  intro g _
  congr 1
  simp only [hecke_apply, finsum_eq_sum_of_fintype, Finset.mul_sum, smul_eq_mul, mul_one, MonoidHom.id_apply]

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem toK_injective (L : Type) [Field L] [NumberField L] (N : ℕ) : Function.Injective (toK L N) := by
  intro a b h
  apply Units.ext
  ext i j
  have h2 := congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h
  simp [toK] at h2
  exact_mod_cast h2

theorem dC_addS {Y : Type} {m : ℕ} (F F' : (Fin (m + 1) → Y) → ℝ) (c : ℝ) :
    dC (F + c • F') = dC F + c • dC F' := by
  funext y
  simp only [dC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dC_zeroS {Y : Type} {m : ℕ} : dC (0 : (Fin (m + 1) → Y) → ℝ) = 0 := by
  funext y
  simp [dC]

theorem hecke_zero {G H K Y : Type} [Group G] [Group H] [Group K] [MulAction H Y] (ρ : G →* K) (τ : K →* H)
    (q : K) : hecke ρ τ q (0 : Y → ℝ) = 0 := by
  funext y
  simp [hecke]

section
variable {G H Y : Type} [Group G] [Group H] [MulAction H Y]

theorem ev_fadd1 (ρ : G →* H) {m : ℕ} (F F' : (Fin (m + 1) → Y) → ℝ) (y : Y) (z : Chn G m) :
    ev ρ (F + F') y z = ev ρ F y z + ev ρ F' y z := by
  unfold ev
  simp only [Pi.add_apply, mul_add]
  exact Finsupp.sum_add

theorem ev_fsmul (ρ : G →* H) {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (c : ℝ) (y : Y) (z : Chn G m) :
    ev ρ (c • F) y z = c * ev ρ F y z := by
  unfold ev
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun g _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

end

def invCoc (L : Type) [Field L] [NumberField L] (n k : ℕ) : Submodule ℝ ((Fin (k + 2) → GK L n) → ℝ) where
  carrier := {G | Inv (toK L n) G ∧ dC G = 0}
  add_mem' := fun {F F'} hF hF' => ⟨fun g y => by
      simp only [Pi.add_apply]
      rw [hF.1, hF'.1], by
      have h := dC_addS F F' 1
      rw [one_smul, one_smul] at h
      rw [h, hF.2, hF'.2, add_zero]⟩
  zero_mem' := ⟨fun _ _ => rfl, dC_zeroS⟩
  smul_mem' := fun c F hF => ⟨fun g y => by
      simp only [Pi.smul_apply]
      rw [hF.1], by
      have h := dC_addS 0 F c
      rw [zero_add, dC_zeroS, zero_add] at h
      rw [h, hF.2, smul_zero]⟩

def resF (L : Type) [Field L] [NumberField L] (n r k : ℕ) (G : (Fin (k + 2) → GK L (n + r)) → ℝ) :
    (Fin (k + 2) → GK L n) → ℝ :=
  fun y => G fun j => stab L n (n + r) (Nat.le_add_right n r) (y j)

private theorem lift_map_comp {V ι : Type} [AddCommGroup V] [Module ℝ V] [Fintype ι]
    (P Q : V →ₗ[ℝ] (ι → ℝ)) (h : ∀ v, P v = 0 → Q v = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖Q v‖ ≤ K * ‖P v‖ := by
  have hk : LinearMap.ker P ≤ LinearMap.ker Q := fun v hv => h v hv
  obtain ⟨M, hM⟩ := LinearMap.exists_extend (((LinearMap.ker P).liftQ Q hk).comp
    (P.quotKerEquivRange.symm : LinearMap.range P →ₗ[ℝ] V ⧸ LinearMap.ker P))
  refine ⟨‖LinearMap.toContinuousLinearMap M‖, norm_nonneg _, fun v => ?_⟩
  have hv : Q v = M (P v) := by
    have := LinearMap.congr_fun hM ⟨P v, LinearMap.mem_range_self P v⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  rw [hv]
  exact (LinearMap.toContinuousLinearMap M).le_opNorm (P v)

private theorem eq_zero_of_mem_all_maximalIdeal_pow {G : Type} [Group G] {k : ℕ} (E : Chn G (k + 1) →ₗ[ℝ] ℝ)
    (s : Finset (Chn G (k + 1)))
    (hs : ∀ z, IsCyc z → ∃ z' ∈ Submodule.span ℝ (s : Set (Chn G (k + 1))), IsBd (z - z'))
    (hbd : ∀ z, IsBd z → E z = 0) (h0 : ∀ z ∈ s, E z = 0) : ∀ z, IsCyc z → E z = 0 := by
  intro z hz
  obtain ⟨z', hz', hb⟩ := hs z hz
  have h1 : z' ∈ LinearMap.ker E :=
    (Submodule.span_le (p := LinearMap.ker E)).2 (fun w hw => h0 w hw) hz'
  have h2 := hbd _ hb
  rw [map_sub, LinearMap.mem_ker.1 h1, sub_zero] at h2
  exact h2

private theorem ev_resF_eq_ev_cmap_stab (L : Type) [Field L] [NumberField L] (n r k : ℕ)
    (hc : ∀ c : Gm L n, toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c) =
      stab L n (n + r) (Nat.le_add_right n r) (toK L n c))
    (G : (Fin (k + 2) → GK L (n + r)) → ℝ) (z : Chn (Gm L n) (k + 1)) :
    ev (toK L n) (resF L n r k G) 1 z =
      ev (toK L (n + r)) G 1 (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z) := by
  unfold ev cmap
  rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by ring)]
  refine Finsupp.sum_congr fun g _ => ?_
  simp only [resF, smul_eq_mul, mul_one, ← map_partialProd, hc]

private theorem exists_linearMap_eq_ev {G : Type} [Group G] {H Y : Type} [Group H] [MulAction H Y] (ρ : G →* H)
    {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) (y : Y) :
    ∃ E : Chn G m →ₗ[ℝ] ℝ, ∀ z, E z = ev ρ F y z := by
  refine ⟨Finsupp.lsum ℝ fun g => LinearMap.id.smulRight (F fun j => ρ (Fin.partialProd g j) • y),
    fun z => ?_⟩
  rw [Finsupp.lsum_apply]
  unfold ev
  refine Finsupp.sum_congr fun g _ => ?_
  simp [smul_eq_mul]

theorem assemble (hCh : SChain) (hEv : SEv) (hSt : SStab) (hFin : SFin) (hAff : SAff) (hKey : PKey)
    (hF : PHeckeFormal) (hK : PHeckeKer) (hI : PIndex) (hSK : PStabK) : SHecke := by
  unfold SHecke
  intro L _ _ hL k hk π hπ
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hCh' := hCh
  obtain ⟨_, hcm, _, _⟩ := hCh
  have hbdmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsBd w →
      IsBd (cmap f (k + 1) w) := by
    intro G H _ _ f w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨cmap f (k + 2) v, hcm G H f (k + 1) v⟩
  have hcycmap : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (w : Chn G (k + 1)), IsCyc w →
      IsCyc (cmap f (k + 1) w) := by
    intro G H _ _ f w hw
    unfold IsCyc at *
    rw [hcm, hw, map_zero]
  set n := 2 * (k + 1) + 4 with hn_def
  have hn1 : 1 ≤ n := by omega
  obtain ⟨s, hs1, hs2⟩ := hFin L hL n k
  have hfinn := (hI L n π hπ).1
  let P : invCoc L n k →ₗ[ℝ] (↥s → ℝ) :=
    { toFun := fun H z₀ => ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z₀.1
      map_add' := fun H H' => by
        funext z₀
        simp only [Submodule.coe_add, ev_fadd1, Pi.add_apply]
      map_smul' := fun c H => by
        funext z₀
        simp only [Submodule.coe_smul, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  let Q : invCoc L n k →ₗ[ℝ] (↥s → ℝ) :=
    { toFun := fun H z₀ => ev (toK L n) (hecke (toK L n) (MonoidHom.id (GK L n)) (qel L n π hπ0)
        (H : (Fin (k + 2) → GK L n) → ℝ)) 1 z₀.1
      map_add' := fun H H' => by
        funext z₀
        have h1 := (hF _ _ (toK L n) _ hfinn (k + 1) H H' 1 H.2.1).2.2
        rw [one_smul, one_smul] at h1
        simp only [Submodule.coe_add, h1, ev_fadd1, Pi.add_apply]
      map_smul' := fun c H => by
        funext z₀
        have h1 := (hF _ _ (toK L n) _ hfinn (k + 1) 0 H c (fun _ _ => rfl)).2.2
        rw [zero_add, hecke_zero, zero_add] at h1
        simp only [Submodule.coe_smul, h1, ev_fsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hPQ : ∀ H, P H = 0 → Q H = 0 := by
    intro H hH
    have hvan : ∀ z : Chn (Gm L n) (k + 1), IsCyc z → ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) 1 z = 0 := by
      obtain ⟨E, hE⟩ := exists_linearMap_eq_ev (toK L n) (H : (Fin (k + 2) → GK L n) → ℝ) (1 : GK L n)
      intro z hz
      rw [← hE]
      refine eq_zero_of_mem_all_maximalIdeal_pow E s hs2 (fun w hw => ?_) (fun w hw => ?_) z hz
      · rw [hE]
        exact (hEv _ _ _ (toK L n) k _ H.2.1 H.2.2).1 1 w hw
      · rw [hE]
        exact congrFun hH ⟨w, hw⟩
    funext z₀
    exact hK hEv _ _ (toK L n) (toK_injective L n) _ hfinn k _ H.2.1 H.2.2 hvan z₀.1 (hs1 _ z₀.2)
  obtain ⟨K, hK0, hKb⟩ := lift_map_comp P Q hPQ
  set i0 : ℝ := ((Gq (toK L n) (qel L n π hπ0)).index : ℝ) with hi0_def
  refine ⟨n + 1 + ⌈5 * (1 + K) * i0⌉₊, fun N hN F hFi hFc hdec z hz => ?_⟩
  obtain ⟨r, rfl⟩ : ∃ r, N = n + r := ⟨N - n, by omega⟩
  have hr : 1 ≤ r := by omega
  have hfinN := hI L (n + r) π hπ
  set iN : ℝ := ((Gq (toK L (n + r)) (qel L (n + r) π hπ0)).index : ℝ) with hiN_def
  have hiN : ((n + r : ℕ) : ℝ) ≤ iN := Nat.cast_le.2 hfinN.2
  have hi0 : 0 ≤ i0 := Nat.cast_nonneg _
  have hceil : 5 * (1 + K) * i0 ≤ iN := by
    have h1 := Nat.le_ceil (5 * (1 + K) * i0)
    have h2 : ((n + 1 + ⌈5 * (1 + K) * i0⌉₊ : ℕ) : ℝ) ≤ ((n + r : ℕ) : ℝ) := by exact_mod_cast hN
    push_cast at h2 hiN
    linarith
  have hiNpos : 0 < iN := by
    have h1 : (1 : ℝ) ≤ ((n + r : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + r)
    linarith
  set a : ℝ := i0 / iN with ha
  have ha0 : 0 ≤ a := div_nonneg hi0 hiNpos.le
  have haK : a * (1 + K) ≤ 1 / 5 := by
    rw [ha, div_mul_eq_mul_div, div_le_iff₀ hiNpos]
    linarith
  have ha15 : a ≤ 1 / 5 := by nlinarith [mul_nonneg ha0 hK0]
  set TN : ((Fin (k + 2) → GK L (n + r)) → ℝ) → ((Fin (k + 2) → GK L (n + r)) → ℝ) := hecke (toK L (n + r)) (MonoidHom.id (GK L (n + r))) (qel L (n + r) π hπ0) with hTN
  have hit : ∀ j, Inv (toK L (n + r)) (TN^[j] F) ∧ dC (TN^[j] F) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨hFi, hFc⟩
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2, _⟩ := hF _ _ (toK L (n + r)) _ hfinN.1 (k + 1) (TN^[j] F) 0 0 ih.1
      refine ⟨h1, ?_⟩
      rw [h2, ih.2, hecke_zero]
  have hc := (hSK L π hπ0 n r hn1).1
  have hres : ∀ G : (Fin (k + 2) → GK L (n + r)) → ℝ, Inv (toK L (n + r)) G → dC G = 0 →
      resF L n r k G ∈ invCoc L n k := by
    intro G hGi hGc
    refine ⟨fun g y => ?_, ?_⟩
    · have h1 := hGi (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) g)
        (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))
      rw [hc] at h1
      simp only [resF, smul_eq_mul, map_mul] at h1 ⊢
      exact h1
    · funext y
      have h1 := congrFun hGc (fun j => stab L n (n + r) (Nat.le_add_right n r) (y j))
      simpa [dC, resF] using h1
  let x : ℕ → (↥s → ℝ) := fun j z₀ => ev (toK L (n + r)) (TN^[j] F) 1
    (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀.1)
  have hstep : ∀ j, (4 / 5 : ℝ) * ‖x j‖ ≤ ‖x (j + 1)‖ := by
    intro j
    have hy : ‖Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩‖ ≤ K * ‖x j‖ := by
      have hP : P ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ = x j :=
        funext fun z₀ => ev_resF_eq_ev_cmap_stab L n r k hc _ z₀.1
      rw [← hP]
      exact hKb _
    have hxy : (1 - a) • x j = x (j + 1) - a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ := by
      funext z₀
      have h1' : x (j + 1) z₀ = (1 - a) * x j z₀ +
          a * Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩ z₀ := by
        have h1 := hKey hCh' hEv hAff L hL k hk π hπ n r hn1 hr (TN^[j] F) (hit j).1 (hit j).2 z₀.1
          (hs1 _ z₀.2)
        simp only [x, Function.iterate_succ_apply']
        exact h1
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [h1']
      ring
    have h1 := norm_sub_le (x (j + 1)) (a • Q ⟨resF L n r k (TN^[j] F), hres _ (hit j).1 (hit j).2⟩)
    rw [← hxy, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0,
      abs_of_nonneg (by linarith)] at h1
    have h2 := mul_le_mul_of_nonneg_left hy ha0
    have h3 := mul_le_mul_of_nonneg_right haK (norm_nonneg (x j))
    nlinarith [norm_nonneg (x j)]
  have hlow : ∀ j, (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ ‖x j‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      nlinarith [hstep j, ih]
  have hdec' : ∀ z₀ : ↥s, ∃ C : ℝ, ∀ j, |x j z₀| ≤ C * (3 / 5) ^ j :=
    fun z₀ => hdec _ (hcycmap _ _ (hs1 _ z₀.2))
  choose C hC using hdec'
  have hup : ∀ j, ‖x j‖ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j := by
    intro j
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun z₀ => ?_
    rw [Real.norm_eq_abs]
    calc |x j z₀| ≤ C z₀ * (3 / 5) ^ j := hC z₀ j
      _ ≤ |C z₀| * (3 / 5) ^ j := by gcongr; exact le_abs_self _
      _ ≤ (∑ z₀, |C z₀|) * (3 / 5) ^ j := by
        gcongr
        exact Finset.single_le_sum (f := fun z => |C z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ z₀)
  have hx0 : ‖x 0‖ = 0 := by
    set D := ∑ z₀, |C z₀|
    have hb : ∀ j, ‖x 0‖ ≤ D * (3 / 4) ^ j := by
      intro j
      have h1 := (hlow j).trans (hup j)
      have hp : (0 : ℝ) < (4 / 5) ^ j := by positivity
      have h2 : (3 / 5 : ℝ) ^ j = (3 / 4) ^ j * (4 / 5) ^ j := by rw [← mul_pow]; norm_num
      rw [h2] at h1
      have h3 : (4 / 5 : ℝ) ^ j * ‖x 0‖ ≤ (4 / 5) ^ j * (D * (3 / 4) ^ j) := by linarith
      exact le_of_mul_le_mul_left h3 hp
    have ht : Filter.Tendsto (fun j : ℕ => D * (3 / 4 : ℝ) ^ j) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
        (by norm_num)).const_mul D
    exact le_antisymm (ge_of_tendsto' ht hb) (norm_nonneg _)
  have hx0' : ∀ z₀ ∈ s, ev (toK L (n + r)) F 1
      (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1) z₀) = 0 := by
    intro z₀ hz₀
    exact congrFun (norm_eq_zero.1 hx0) ⟨z₀, hz₀⟩
  obtain ⟨E, hE⟩ := exists_linearMap_eq_ev (toK L (n + r)) F (1 : GK L (n + r))
  have hall := eq_zero_of_mem_all_maximalIdeal_pow (E.comp (cmap (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)) (k + 1))) s hs2
    (fun w hw => by
      rw [LinearMap.comp_apply, hE]
      exact (hEv _ _ _ _ k F hFi hFc).1 1 _ (hbdmap _ w hw))
    (fun w hw => by
      rw [LinearMap.comp_apply, hE]
      exact hx0' w hw)
  obtain ⟨z₀, hz₀, hb⟩ := (hSt (𝓞 L) k n (n + r) (Nat.le_add_right n r) (le_refl _)).2 z hz
  have h1 := (hEv _ _ _ _ k F hFi hFc).1 1 _ hb
  have h2 := hall z₀ hz₀
  rw [← hE, map_sub] at h1
  rw [LinearMap.comp_apply] at h2
  rw [← hE]
  linarith

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section
noncomputable section

open UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section
variable {Γn ΓN Kn KN : Type} [Group Γn] [Group ΓN] [Group Kn] [Group KN]
  {ρn : Γn →* Kn} {ρN : ΓN →* KN} {sO : Γn →* ΓN} {sL : Kn →* KN} {qn : Kn} {q : KN}

private theorem ev_one_eq_finsupp_sum {G K : Type} [Group G] [Group K] (ρ : G →* K) {m : ℕ}
    (Ψ : (Fin (m + 2) → K) → ℝ) (z : Chn G (m + 1)) :
    ev ρ Ψ 1 z = Finsupp.sum (α := Fin (m + 1) → G) z
      (fun g r => r * Ψ (fun j => ρ (Fin.partialProd g j))) := by
  unfold ev
  simp only [smul_eq_mul, mul_one]

private theorem partialProd_map_monoidHom {G G' : Type} [Group G] [Group G'] (s : G' →* G) {n : ℕ} (g : Fin n → G')
    (j : Fin (n + 1)) : Fin.partialProd (fun i => s (g i)) j = s (Fin.partialProd g j) := by
  unfold Fin.partialProd
  rw [map_list_prod, List.map_take, List.map_ofFn]
  rfl

private theorem ev_one_cmap_eq_finsupp_sum {G K G' : Type} [Group G] [Group K] [Group G'] (ρ : G →* K)
    (s : G' →* G) {m : ℕ} (Ψ : (Fin (m + 2) → K) → ℝ) (z : Chn G' (m + 1)) :
    ev ρ Ψ 1 (cmap s (m + 1) z) = Finsupp.sum (α := Fin (m + 1) → G') z
      (fun g r => r * Ψ (fun j => ρ (s (Fin.partialProd g j)))) := by
  rw [ev_one_eq_finsupp_sum]
  unfold cmap
  rw [Finsupp.lmapDomain_apply, Finsupp.sum_mapDomain_index]
  · congr 1
    funext g r
    congr 2
    funext j
    congr 1
    exact partialProd_map_monoidHom s g j
  · intro _
    simp
  · intro _ _ _
    ring

private theorem ev_sub_hecke_double_cosets {G H Y : Type} [Group G] [Group H] [MulAction H Y] (ρ : G →* H) {m : ℕ}
    (f g : (Fin (m + 1) → Y) → ℝ) (y : Y) (w : Chn G m) :
    ev ρ (fun t => f t - g t) y w = ev ρ f y w - ev ρ g y w := by
  unfold ev
  simp only [mul_sub]
  exact Finsupp.sum_sub

private theorem coset_lemma_4 {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) {m : ℕ}
    (F : (Fin (m + 2) → K) → ℝ) (hF : Inv ρ F) {c c' : G} (h : c' * c⁻¹ ∈ Gq ρ q)
    (w : Fin (m + 2) → K) :
    F (fun j => q * ρ c' * w j) = F (fun j => q * ρ c * w j) := by
  unfold Gq at h
  rw [Subgroup.mem_comap, Subgroup.mem_map] at h
  obtain ⟨a, ha1, ha⟩ := h
  obtain ⟨g', rfl⟩ := MonoidHom.mem_range.mp ha1
  simp at ha
  have hc' : ρ c' = q⁻¹ * ρ g' * q * ρ c := by
    rw [ha]
    group
  have e : (fun j => q * ρ c' * w j) = fun j => ρ g' • (q * ρ c * w j) := by
    funext j
    rw [hc', smul_eq_mul]
    group
  rw [e]
  exact hF g' _

private theorem hecke_apply_eq_index_inv_mul_finsum_rightRel {G K : Type} [Group G] [Group K] (ρ : G →* K) (q : K) {m : ℕ}
    (Ψ : (Fin (m + 2) → K) → ℝ) (y : Fin (m + 2) → K) :
    hecke ρ (MonoidHom.id K) q Ψ y = ((Gq ρ q).index : ℝ)⁻¹ *
      ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρ q)), Ψ (fun j => q * ρ c.out * y j) := by
  unfold hecke
  rfl

private theorem quotient_mk_rightRel_eq_iff_mul_inv_mem {G : Type} [Group G] (S : Subgroup G) (a b : G) :
    Quotient.mk (QuotientGroup.rightRel S) a = Quotient.mk (QuotientGroup.rightRel S) b ↔
      b * a⁻¹ ∈ S := by
  rw [Quotient.eq]
  exact QuotientGroup.rightRel_apply

private theorem index_eq_card_quotient_rightRel {G : Type} [Group G] (S : Subgroup G)
    [Fintype (Quotient (QuotientGroup.rightRel S))] :
    (S.index : ℝ) = Fintype.card (Quotient (QuotientGroup.rightRel S)) := by
  rw [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S)]

theorem keyGen (hT : PTransfer) (hcomm : ∀ c, ρN (sO c) = sL (ρn c)) (hq : q = sL qn)
    (hGS : ∀ c, sO c ∈ Gq ρN q ↔ c ∈ Gq ρn qn)
    [Finite (Quotient (QuotientGroup.rightRel (Gq ρN q)))] [Finite (Quotient (QuotientGroup.rightRel (Gq ρn qn)))]
    (m : ℕ) (F : (Fin (m + 2) → KN) → ℝ) (hFinv : Inv ρN F) (hFcoc : dC F = 0)
    (hvan : ∀ c : ΓN, (∀ c' : Γn, c * (sO c')⁻¹ ∉ Gq ρN q) → ∀ H : Subgroup Γn,
      (∀ h ∈ H, c * sO h * c⁻¹ ∈ Gq ρN q) → ∀ w : Chn H (m + 1), IsCyc w →
        ev H.subtype (fun y => F fun j => q * ρN c * ρN (sO (y j))) 1 w =
          ev H.subtype (fun y => F fun j => ρN (sO (y j))) 1 w)
    (z : Chn Γn (m + 1)) (hz : IsCyc z) :
    ev ρN (hecke ρN (MonoidHom.id KN) q F) 1 (cmap sO (m + 1) z) =
      (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * ev ρN F 1 (cmap sO (m + 1) z) +
        ((Gq ρn qn).index : ℝ) / (Gq ρN q).index *
          ev ρn (hecke ρn (MonoidHom.id Kn) qn (fun y => F fun j => sL (y j))) 1 z := by
  classical
  rw [ev_one_cmap_eq_finsupp_sum, ev_one_cmap_eq_finsupp_sum, ev_one_eq_finsupp_sum]
  simp only [hecke_apply_eq_index_inv_mul_finsum_rightRel]
  have hT' := hT
  unfold PTransfer at hT'
  let X := {x : Quotient (QuotientGroup.rightRel (Gq ρN q)) //
    ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ x}
  have hmem : ∀ (x : X) (g : Γn) (a : Γn), Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠
      Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g) := by
    intro x g a ha
    rw [quotient_mk_rightRel_eq_iff_mul_inv_mem] at ha
    apply x.2 (a * g⁻¹)
    rw [← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]
    convert ha using 1
    rw [map_mul, map_inv]
    group
  obtain ⟨act, hact⟩ : ∃ act : X → Γn → X, ∀ x g,
      (act x g).1 = Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (x.1.out * sO g) :=
    ⟨fun x g => ⟨_, hmem x g⟩, fun _ _ => rfl⟩
  have hrep : ∀ (x : X) (g : Γn), (act x g).1.out * (x.1.out * sO g)⁻¹ ∈ Gq ρN q := by
    intro x g
    rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, hact]
  have h1 : ∀ x, act x 1 = x := by
    intro x
    apply Subtype.ext
    rw [hact, map_one, mul_one, Quotient.out_eq]
  have hm : ∀ x g h, act x (g * h) = act (act x g) h := by
    intro x g h
    apply Subtype.ext
    rw [hact, hact, quotient_mk_rightRel_eq_iff_mul_inv_mem]
    convert hrep x g using 1
    rw [map_mul]
    group
  let Φ : X → (Fin (m + 2) → Γn) → ℝ := fun x y =>
    F (fun j => q * ρN x.1.out * ρN (sO (y j))) - F (fun j => ρN (sO (y j)))
  have hΦ1 : ∀ x g y, Φ (act x g) y = Φ x (fun j => g * y j) := by
    intro x g y
    simp only [Φ]
    rw [coset_lemma_4 ρN q F hFinv (hrep x g) (fun j => ρN (sO (y j)))]
    congr 1
    · congr 1
      funext j
      simp [map_mul, mul_assoc]
    · rw [show (fun j => ρN (sO (g * y j))) = fun j => ρN (sO g) • ρN (sO (y j)) from
        funext fun j => by simp]
      exact (hFinv _ _).symm
  have hΦ2 : ∀ x, dC (Φ x) = 0 := by
    intro x
    funext y
    have e1 := congrFun hFcoc (fun j => q * ρN x.1.out * ρN (sO (y j)))
    have e2 := congrFun hFcoc (fun j => ρN (sO (y j)))
    simp only [dC, Pi.zero_apply, Φ] at e1 e2 ⊢
    simp only [mul_sub, Finset.sum_sub_distrib, e1, e2, sub_zero]
  have hΦ3 : ∀ x (w : Chn (stabR act h1 hm x) (m + 1)), IsCyc w →
      ev (stabR act h1 hm x).subtype (Φ x) 1 w = 0 := by
    intro x w hw
    have hx : ∀ c' : Γn, x.1.out * (sO c')⁻¹ ∉ Gq ρN q := by
      intro c' hc
      apply x.2 c'
      rw [← Quotient.out_eq x.1, quotient_mk_rightRel_eq_iff_mul_inv_mem]
      exact hc
    have hst : ∀ h ∈ stabR act h1 hm x, x.1.out * sO h * x.1.out⁻¹ ∈ Gq ρN q := by
      intro h hh
      have hh' : act x h = x := hh
      have e := congrArg Subtype.val hh'
      rw [hact] at e
      conv at e => rhs; rw [← Quotient.out_eq x.1]
      exact (quotient_mk_rightRel_eq_iff_mul_inv_mem _ _ _).mp e.symm
    have e := hvan x.1.out hx _ hst w hw
    show ev _ (fun t => F (fun j => q * ρN x.1.out * ρN (sO (t j))) - F (fun j => ρN (sO (t j)))) 1 w = 0
    rw [ev_sub_hecke_double_cosets, e, sub_self]
  haveI : Finite X := Subtype.finite
  have hz0 := hT' Γn X act h1 hm m Φ hΦ1 hΦ2 hΦ3 z hz
  rw [ev_one_eq_finsupp_sum] at hz0
  simp only [MonoidHom.id_apply] at hz0
  haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρN q))) := Fintype.ofFinite _
  haveI : Fintype (Quotient (QuotientGroup.rightRel (Gq ρn qn))) := Fintype.ofFinite _
  haveI : Fintype X := Fintype.ofFinite _
  have himg : Finset.univ.filter (fun c : Quotient (QuotientGroup.rightRel (Gq ρN q)) =>
      ¬ ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) =
      Finset.univ.image (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) =>
        Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, not_forall, not_not]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Quotient.mk (QuotientGroup.rightRel (Gq ρn qn)) a, ?_⟩
      rw [← ha, quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]
    · rintro ⟨d, hd⟩
      exact ⟨d.out, hd⟩
  have hinj : Function.Injective (fun d : Quotient (QuotientGroup.rightRel (Gq ρn qn)) =>
      Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    intro d d' h
    simp only at h
    rw [quotient_mk_rightRel_eq_iff_mul_inv_mem, ← map_inv, ← map_mul, hGS, ← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq, Quotient.out_eq] at h
    exact h
  have hgen : ∀ f : Quotient (QuotientGroup.rightRel (Gq ρN q)) → ℝ,
      ∑ c, f c = ∑ x : X, f x.1 +
        ∑ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
          f (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)) := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c => ∀ a : Γn, Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO a) ≠ c) f,
      himg, Finset.sum_image (fun x _ y _ h => hinj h), Finset.sum_subtype _ (fun x => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ _)))]
  have hNpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρN q))) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩
  have hnpos : 0 < Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ 1⟩
  have hcard := hgen (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcard
  have hpt : ∀ y : Fin (m + 2) → Γn,
      ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρN q)),
          F (fun j => q * ρN c.out * ρN (sO (y j))) =
        (1 - ((Gq ρn qn).index : ℝ) / (Gq ρN q).index) * F (fun j => ρN (sO (y j))) +
          ((Gq ρn qn).index : ℝ) / (Gq ρN q).index * (((Gq ρn qn).index : ℝ)⁻¹ *
            ∑ᶠ c : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
              F (fun j => sL (qn * ρn c.out * ρn (y j)))) +
          ((Gq ρN q).index : ℝ)⁻¹ * ∑ᶠ x : X, Φ x y := by
    intro y
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, index_eq_card_quotient_rightRel,
      index_eq_card_quotient_rightRel, hgen]
    have hd : ∀ d : Quotient (QuotientGroup.rightRel (Gq ρn qn)),
        F (fun j => q * ρN (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out *
          ρN (sO (y j))) = F (fun j => sL (qn * ρn d.out * ρn (y j))) := by
      intro d
      rw [coset_lemma_4 ρN q F hFinv (c := sO d.out)
        (c' := (Quotient.mk (QuotientGroup.rightRel (Gq ρN q)) (sO d.out)).out)
        (by rw [← quotient_mk_rightRel_eq_iff_mul_inv_mem, Quotient.out_eq]) (fun j => ρN (sO (y j)))]
      congr 1
      funext j
      simp only [hq, hcomm, map_mul]
    simp only [hd, Φ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard]
    have h1' : (Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hnpos.ne'
    have h2' : (Fintype.card X : ℝ) + Fintype.card (Quotient (QuotientGroup.rightRel (Gq ρn qn))) ≠ 0 := by
      positivity
    field_simp
    ring
  simp only [hpt]
  rw [← sub_eq_zero]
  calc _ = ((Gq ρN q).index : ℝ)⁻¹ *
        Finsupp.sum z (fun g r => r * ∑ᶠ x : X, Φ x (fun j => Fin.partialProd g j)) := by
        simp only [Finsupp.sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro g _
        ring
    _ = 0 := by rw [hz0, mul_zero]

end

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section Perm

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem permMatrix_apply' (σ : Equiv.Perm n) (i j : n) :
    (σ.permMatrix R) i j = if σ i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

theorem permMatrix_mul_apply (σ τ : Equiv.Perm n) (i j : n) :
    (σ.permMatrix R * τ.permMatrix R) i j = if τ (σ i) = j then 1 else 0 := by
  simp only [Matrix.mul_apply, permMatrix_apply', ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

def permU (σ : Equiv.Perm n) : GL n R :=
  ⟨σ.permMatrix R, σ⁻¹.permMatrix R, by
    ext i j
    rw [permMatrix_mul_apply, Matrix.one_apply]
    simp, by
    ext i j
    rw [permMatrix_mul_apply, Matrix.one_apply]
    simp⟩

theorem permU_coe (σ : Equiv.Perm n) : ((permU σ : GL n R) : Matrix n n R) = σ.permMatrix R := rfl

theorem permU_inv_coe (σ : Equiv.Perm n) : (((permU σ)⁻¹ : GL n R) : Matrix n n R) = σ⁻¹.permMatrix R := rfl

end Perm

section Basic

variable {L : Type} [Field L] [NumberField L]

theorem qel_coe (N : ℕ) (π : 𝓞 L) (hπ : π ≠ 0) :
    ((qel L N π hπ : GK L N) : Matrix (Fin N) (Fin N) L) =
      diagonal fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1 := rfl

theorem toK_coe (N : ℕ) (γ : Gm L N) (i j : Fin N) :
    ((toK L N γ : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) i j =
      algebraMap (𝓞 L) L ((γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j) := rfl

theorem algebraMap_inj : Function.Injective (algebraMap (𝓞 L) L) :=
  FaithfulSMul.algebraMap_injective (𝓞 L) L

theorem mem_Gq_iff' (N : ℕ) (π : 𝓞 L) (hπ : π ≠ 0) (γ : Gm L N) :
    γ ∈ Gq (toK L N) (qel L N π hπ) ↔ ∃ δ : Gm L N, toK L N δ * qel L N π hπ = qel L N π hπ * toK L N γ := by
  constructor
  · intro h
    obtain ⟨x, ⟨δ, rfl⟩, hx⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 h)
    refine ⟨δ, ?_⟩
    have hx' : (qel L N π hπ)⁻¹ * toK L N δ * qel L N π hπ = toK L N γ := by
      simpa [MulAut.conj_apply] using hx
    rw [← hx']
    group
  · rintro ⟨δ, h⟩
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨toK L N δ, ⟨δ, rfl⟩, ?_⟩)
    show (MulAut.conj (qel L N π hπ)⁻¹) (toK L N δ) = toK L N γ
    rw [MulAut.conj_apply, inv_inv, mul_assoc, h]
    group

theorem mem_Gq_iff (N : ℕ) (π : 𝓞 L) (hπ : π ≠ 0) (γ : Gm L N) :
    γ ∈ Gq (toK L N) (qel L N π hπ) ↔
      ∀ i j : Fin N, (j : ℕ) = 0 → (i : ℕ) ≠ 0 → (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j ∈ Ideal.span {π} := by
  rw [mem_Gq_iff']
  constructor
  · rintro ⟨δ, h⟩ i j hj hi
    have e := congrArg (fun g : GL (Fin N) L => (g : Matrix (Fin N) (Fin N) L) i j) h
    simp only [Units.val_mul, qel_coe, Matrix.mul_diagonal, Matrix.diagonal_mul, hj, hi, if_true,
      if_false, toK_coe, one_mul] at e
    rw [Ideal.mem_span_singleton']
    refine ⟨(δ : Matrix (Fin N) (Fin N) (𝓞 L)) i j, algebraMap_inj ?_⟩
    rw [map_mul]
    exact e
  · intro h
    have hd : ∀ i j : Fin N, (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 →
        ∃ a : 𝓞 L, a * π = (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j := fun i j hij =>
      Ideal.mem_span_singleton'.1 (h i j hij.1 hij.2)
    let M : Matrix (Fin N) (Fin N) (𝓞 L) := Matrix.of fun i j =>
      if hij : (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 then Classical.choose (hd i j hij)
      else if (i : ℕ) = 0 ∧ (j : ℕ) ≠ 0 then π * (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j
      else (γ : Matrix (Fin N) (Fin N) (𝓞 L)) i j
    have hM : M.map (algebraMap (𝓞 L) L) * diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) =
        diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1) *
          (γ : Matrix (Fin N) (Fin N) (𝓞 L)).map (algebraMap (𝓞 L) L) := by
      ext i j
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, M, Matrix.of_apply]
      by_cases hj : (j : ℕ) = 0 <;> by_cases hi : (i : ℕ) = 0
      · rw [dif_neg (by tauto), if_neg (by tauto), if_pos hj, if_pos hi, mul_comm]
      · rw [dif_pos ⟨hj, hi⟩, if_pos hj, if_neg hi, one_mul]
        have hs := Classical.choose_spec (hd i j ⟨hj, hi⟩)
        calc _ = algebraMap (𝓞 L) L (Classical.choose (hd i j ⟨hj, hi⟩) * π) := by rw [map_mul]
          _ = _ := by rw [hs]
      · rw [dif_neg (by tauto), if_pos ⟨hi, hj⟩, if_neg hj, if_pos hi, mul_one, map_mul]
      · rw [dif_neg (by tauto), if_neg (by tauto), if_neg hj, if_neg hi, mul_one, one_mul]
    have hdet : M.det = (γ : Matrix (Fin N) (Fin N) (𝓞 L)).det := by
      apply algebraMap_inj
      have e := congrArg Matrix.det hM
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm] at e
      have hne : (diagonal (fun i : Fin N => if (i : ℕ) = 0 then (π : L) else 1)).det ≠ 0 := by
        rw [Matrix.det_diagonal]
        refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
        split_ifs
        · exact fun h0 => hπ (algebraMap_inj (by simpa using h0))
        · exact one_ne_zero
      have e' := mul_left_cancel₀ hne e
      rw [RingHom.map_det, RingHom.map_det]
      exact e'
    have hu : IsUnit M.det := hdet ▸ Matrix.isUnits_det_units γ
    refine ⟨⟨M, M⁻¹, Matrix.mul_nonsing_inv M hu, Matrix.nonsing_inv_mul M hu⟩, ?_⟩
    apply Units.ext
    simp only [Units.val_mul, qel_coe]
    exact hM

end Basic

section Index

variable {L : Type} [Field L] [NumberField L]

theorem span_isMaximal {π : 𝓞 L} (hπ : Prime π) : (Ideal.span {π} : Ideal (𝓞 L)).IsMaximal := by
  refine Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hπ.ne_zero

theorem one_not_mem_span {π : 𝓞 L} (hπ : Prime π) : (1 : 𝓞 L) ∉ Ideal.span {π} := fun h =>
  (span_isMaximal hπ).ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem finite_cosets (N : ℕ) (π : 𝓞 L) (hπ : Prime π) :
    Finite (Quotient (QuotientGroup.rightRel (Gq (toK L N) (qel L N π hπ.ne_zero)))) := by
  haveI := span_isMaximal hπ
  rcases N with _ | N
  · haveI : Subsingleton (Gm L 0) := ⟨fun a b => Units.ext (Matrix.ext fun i => i.elim0)⟩
    haveI : Finite (Gm L 0) := Finite.of_subsingleton
    exact Quotient.finite _
  · let f : Quotient (QuotientGroup.rightRel (Gq (toK L (N + 1)) (qel L (N + 1) π hπ.ne_zero))) →
        (Fin (N + 1) → 𝓞 L ⧸ Ideal.span {π}) := fun x l =>
      Ideal.Quotient.mk _ (((x.out⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0)
    refine Finite.of_injective f fun x y hxy => ?_
    rw [← Quotient.out_eq x, ← Quotient.out_eq y]
    apply Quotient.sound
    refine QuotientGroup.rightRel_apply.2 ?_
    rw [mem_Gq_iff]
    intro i j hj hi
    have hj' : j = 0 := Fin.ext hj
    subst hj'
    set a := x.out
    set b := y.out
    have e1 : ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l *
        ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 = 0 := by
      have := congrFun (congrFun (Units.mul_inv b) i) 0
      rw [Matrix.mul_apply] at this
      rw [this, Matrix.one_apply, if_neg]
      exact fun h => hi (by rw [h]; rfl)
    have hmem : ∀ l, ((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 -
        ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 ∈ Ideal.span {π} := fun l =>
      Ideal.Quotient.eq.1 (congrFun hxy l)
    rw [Units.val_mul, Matrix.mul_apply]
    have : ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l *
        ((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 =
        ∑ l, (b : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) i l *
        (((a⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0 -
          ((b⁻¹ : Gm L (N + 1)) : Matrix (Fin (N + 1)) (Fin (N + 1)) (𝓞 L)) l 0) := by
      simp only [mul_sub, Finset.sum_sub_distrib, e1, sub_zero]
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hmem l)

theorem pIndex : PIndex := by
  intro L _ _ N π hπ
  have hfin := finite_cosets N π hπ
  refine ⟨hfin, ?_⟩
  rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  rcases N with _ | N
  · exact Nat.zero_le _
  let g : Fin (N + 1) → Quotient (QuotientGroup.rightRel (Gq (toK L (N + 1)) (qel L (N + 1) π hπ.ne_zero))) :=
    fun j => Quotient.mk _ (permU (Equiv.swap 0 j))
  have hg : Function.Injective g := by
    intro j k hjk
    by_contra hne
    have h := QuotientGroup.rightRel_apply.1 (Quotient.exact hjk)
    rw [mem_Gq_iff] at h
    have hk0 : ((Equiv.swap 0 k) j : ℕ) ≠ 0 := by
      intro h0
      have : (Equiv.swap 0 k) j = 0 := Fin.ext h0
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at this
      exact hne this
    have := h ((Equiv.swap 0 k) j) 0 rfl hk0
    rw [Units.val_mul, permU_coe, permU_inv_coe, permMatrix_mul_apply, if_pos] at this
    · exact one_not_mem_span hπ this
    · simp [Equiv.swap_apply_self]
  have := Nat.card_le_card_of_injective g hg
  simpa using this

end Index

section Stab

variable {L : Type} [Field L] [NumberField L]

theorem pStabK : PStabK := by
  intro L _ _ π hπ n r hn
  constructor
  · intro c
    apply Units.ext
    ext i j
    rw [toK_coe, stab_apply, stab_apply]
    split_ifs with h1 h2
    · rfl
    · simp
    · simp
  · apply Units.ext
    ext i j
    rw [stab_apply, qel_coe, qel_coe]
    simp only [Matrix.diagonal_apply]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem pGqStab : PGqStab := by
  intro L _ _ π hπ n r hn c
  rw [mem_Gq_iff, mem_Gq_iff]
  constructor
  · intro h i j hj hi
    have := h (Fin.castAdd r i) (Fin.castAdd r j) hj hi
    rwa [stab_apply, dif_pos ⟨i.2, j.2⟩] at this
  · intro h i j hj hi
    rw [stab_apply]
    split_ifs with h1 h2
    · exact h _ _ hj hi
    · exact absurd (congrArg Fin.val h2) (by omega)
    · exact Submodule.zero_mem _

end Stab

section Low

variable {R : Type} [CommRing R]

theorem exists_clear (n : ℕ) (hn : 1 ≤ n) (I : Ideal R) (hI : I.IsMaximal) (v : Fin n → R)
    (a : Fin n) (ha : v a ∉ I) :
    ∃ c' : GL (Fin n) R, ∀ i : Fin n, (i : ℕ) ≠ 0 → ((c' : Matrix (Fin n) (Fin n) R) *ᵥ v) i ∈ I := by
  let z : Fin n := ⟨0, hn⟩
  let σ : Equiv.Perm (Fin n) := Equiv.swap z a
  let W : Fin n → R := v ∘ σ
  have hW : W z ∉ I := by simpa [W, σ] using ha
  obtain ⟨s, t, ht, hst⟩ := hI.exists_inv hW
  let Nm : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => if (j : ℕ) = 0 ∧ (i : ℕ) ≠ 0 then s * W i else 0
  have hNN : Nm * Nm = 0 := by
    ext i j
    simp only [Matrix.mul_apply, Nm, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h1 h2 <;> first | simp | exact absurd h1.1 h2.2
  let U : Matrix (Fin n) (Fin n) R := 1 - Nm
  have hU : U * (1 + Nm) = 1 := by
    simp only [U, sub_mul, one_mul, mul_add, mul_one, hNN, add_zero]
    abel
  let M : Matrix (Fin n) (Fin n) R := U * σ.permMatrix R
  have hM : IsUnit M.det := by
    rw [Matrix.det_mul, Matrix.det_permutation]
    refine (Matrix.isUnit_det_of_right_inverse hU).mul ?_
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  refine ⟨⟨M, M⁻¹, Matrix.mul_nonsing_inv M hM, Matrix.nonsing_inv_mul M hM⟩, fun i hi => ?_⟩
  show (M *ᵥ v) i ∈ I
  have e : M *ᵥ v = U *ᵥ W := by
    rw [← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
  rw [e]
  have e3 : (Nm *ᵥ W) i = s * W i * W z := by
    simp only [Matrix.mulVec, dotProduct, Nm, Matrix.of_apply]
    rw [Finset.sum_eq_single z]
    · simp [z, hi]
    · intro b _ hb
      rw [if_neg, zero_mul]
      exact fun h => hb (Fin.ext h.1)
    · simp
  have e2 : (U *ᵥ W) i = W i * t := by
    rw [show U = 1 - Nm from rfl, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, e3,
      show t = 1 - s * W z by rw [← hst]; ring]
    ring
  rw [e2]
  exact I.mul_mem_left _ ht

end Low

theorem pLow : PLow := by
  intro L _ _ π hπ n r hn c hc
  have hmax := span_isMaximal hπ
  let z0 : Fin (n + r) := ⟨0, by omega⟩
  let v : Fin n → 𝓞 L := fun a =>
    ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.castAdd r a) z0
  have hex : ∃ a, v a ∉ Ideal.span {π} := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ l : Fin (n + r),
        ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) l z0 ∈ Ideal.span {π} := by
      intro l
      refine Fin.addCases (fun a => ?_) (fun b => ?_) l
      · exact hcon a
      · exact hc b
    have h1 := congrFun (congrFun (Units.mul_inv c) z0) z0
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    apply one_not_mem_span hπ
    rw [← h1]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hall l)
  obtain ⟨a, ha⟩ := hex
  obtain ⟨c', hc'⟩ := exists_clear n hn _ hmax v a ha
  refine ⟨c', ?_⟩
  rw [← Subgroup.inv_mem_iff, _root_.mul_inv_rev, inv_inv, mem_Gq_iff]
  intro i j hj hi
  have hj' : j = z0 := Fin.ext hj
  subst hj'
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
  cases i using Fin.addCases with
  | left i' =>
    have hi' : (i' : ℕ) ≠ 0 := by simpa using hi
    have e : ∑ b : Fin r, (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) c' : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))
        (Fin.castAdd r i') (Fin.natAdd n b) *
        ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n b) z0 = 0 := by
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [stab_apply, dif_neg (by simp), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega),
        zero_mul]
    rw [e, add_zero]
    have := hc' i' hi'
    simp only [Matrix.mulVec, dotProduct] at this
    convert this using 2 with b _
    rw [stab_apply, dif_pos ⟨by simp, by simp⟩]
    rfl
  | right i' =>
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun b _ => ?_) (Ideal.sum_mem _ fun b _ => ?_)
    · rw [stab_apply, dif_neg (by simp), if_neg (fun h => by have := congrArg Fin.val h; simp at this; omega),
        zero_mul]
      exact Submodule.zero_mem _
    · exact Ideal.mul_mem_left _ _ (hc b)

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section
noncomputable section

open NumberField NumberField.InfinitePlace Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

section Affine

variable {L : Type} [Field L] [NumberField L]

theorem aff_alg_inj : Function.Injective (algebraMap (𝓞 L) L) :=
  FaithfulSMul.algebraMap_injective (𝓞 L) L

theorem aff_toK_val (N : ℕ) (g : Gm L N) (a b : Fin N) :
    (toK L N g : Matrix (Fin N) (Fin N) L) a b =
      algebraMap (𝓞 L) L ((g : Matrix (Fin N) (Fin N) (𝓞 L)) a b) :=
  rfl

theorem aff_toK_inj (N : ℕ) : Function.Injective (toK L N) := by
  intro a b hab
  refine Matrix.GeneralLinearGroup.ext fun x y => aff_alg_inj ?_
  rw [← aff_toK_val, ← aff_toK_val, hab]

theorem aff_toK_stab (n N : ℕ) (h : n ≤ N) (c : Gm L n) :
    toK L N (stab (𝓞 L) n N h c) = stab L n N h (toK L n c) := by
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [aff_toK_val, stab_apply, stab_apply]
  split_ifs <;> simp [aff_toK_val]

end Affine

theorem aff_stab_low {R : Type} [CommRing R] (n r : ℕ) (g : GL (Fin n) R) (i : Fin r) (b : Fin (n + r)) :
    (stab R n (n + r) (Nat.le_add_right n r) g : Matrix (Fin (n + r)) (Fin (n + r)) R) (Fin.natAdd n i) b =
      (1 : Matrix (Fin (n + r)) (Fin (n + r)) R) (Fin.natAdd n i) b := by
  rw [stab_apply, dif_neg (by simp only [Fin.val_natAdd]; omega), Matrix.one_apply]

theorem aff_stab_lowc {R : Type} [CommRing R] (n r : ℕ) (g : GL (Fin n) R) (i : Fin r) (a : Fin (n + r)) :
    (stab R n (n + r) (Nat.le_add_right n r) g : Matrix (Fin (n + r)) (Fin (n + r)) R) a (Fin.natAdd n i) =
      (1 : Matrix (Fin (n + r)) (Fin (n + r)) R) a (Fin.natAdd n i) := by
  rw [stab_apply, dif_neg (by simp only [Fin.val_natAdd]; omega), Matrix.one_apply]

theorem aff_stab_top {R : Type} [CommRing R] (n r : ℕ) (g : GL (Fin n) R) (a b : Fin n) :
    (stab R n (n + r) (Nat.le_add_right n r) g : Matrix (Fin (n + r)) (Fin (n + r)) R) (Fin.castAdd r a)
      (Fin.castAdd r b) = (g : Matrix (Fin n) (Fin n) R) a b := by
  rw [stab_apply, dif_pos (by simp only [Fin.val_castAdd]; exact ⟨a.2, b.2⟩)]
  rfl

theorem aff_conj {K : Type} [Field K] (n r : ℕ) (i : Fin r) (h : GL (Fin n) K) (y : Fin (n + r) → K)
    (G : GL (Fin (n + r)) K)
    (hG : (G : Matrix (Fin (n + r)) (Fin (n + r)) K) =
      1 + vecMulVec (y - Pi.single (Fin.natAdd n i) 1) (Pi.single (Fin.natAdd n i) 1)) :
    ((G⁻¹ * stab K n (n + r) (Nat.le_add_right n r) h * G : GL (Fin (n + r)) K) :
        Matrix (Fin (n + r)) (Fin (n + r)) K) =
      (stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) +
        vecMulVec (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
          (Pi.single (Fin.natAdd n i) 1) := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin (n + r)) (Fin (n + r)) K,
      S = (stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Fin (n + r) → K, e = Pi.single (Fin.natAdd n i) 1 := ⟨_, rfl⟩
  rw [← hS, ← he]
  rw [← he] at hG
  have hrow : ∀ b, S (Fin.natAdd n i) b = (1 : Matrix (Fin (n + r)) (Fin (n + r)) K) (Fin.natAdd n i) b := by
    intro b; rw [hS]; exact aff_stab_low n r h i b
  have hcol : ∀ a, S a (Fin.natAdd n i) = (1 : Matrix (Fin (n + r)) (Fin (n + r)) K) a (Fin.natAdd n i) := by
    intro a; rw [hS]; exact aff_stab_lowc n r h i a
  have h1 : e ᵥ* S = e := by
    funext b
    simp [he, vecMul, dotProduct, Pi.single_apply, hrow, Matrix.one_apply]
    split_ifs with h₁ h₂ h₂ <;> first | rfl | (exfalso; exact h₂ h₁.symm) | (exfalso; exact h₁ h₂.symm)
  have h2 : ((S - 1) *ᵥ y) (Fin.natAdd n i) = 0 := by
    simp [mulVec, dotProduct, Matrix.sub_apply, hrow]
  have h3 : e ᵥ* vecMulVec ((S - 1) *ᵥ y) e = 0 := by
    funext b
    simp only [vecMul, dotProduct, vecMulVec_apply, Pi.zero_apply]
    rw [Finset.sum_eq_single (Fin.natAdd n i)]
    · rw [h2]; ring
    · intro c _ hc; rw [he, Pi.single_apply, if_neg hc]; ring
    · simp
  have h4 : S *ᵥ e = e := by
    funext a
    simp [he, mulVec, dotProduct, Pi.single_apply, hcol, Matrix.one_apply]
  have key : (1 + vecMulVec (y - e) e) * (S + vecMulVec ((S - 1) *ᵥ y) e) = S * (1 + vecMulVec (y - e) e) := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, h1, h3,
      Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_sub, h4]
    ext a b
    simp only [Matrix.add_apply, vecMulVec_apply, Pi.sub_apply, Pi.zero_apply, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    ring
  rw [Units.val_mul, Units.val_mul, ← hS, hG, Matrix.mul_assoc, ← key, ← Matrix.mul_assoc, ← hG,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

section Gamma

variable {L : Type} [Field L] [NumberField L]

theorem aff_gamma (π : 𝓞 L) (hπ : Prime π) (n r : ℕ) (hn : 1 ≤ n) (c : Gm L (n + r)) (i : Fin r)
    (hi : ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n i) ⟨0, by omega⟩ ∉
      Ideal.span {π}) :
    ∃ (y : Fin (n + r) → L) (G : GK L (n + r)) (γ : Gm L (n + r)),
      (G : Matrix (Fin (n + r)) (Fin (n + r)) L) =
        1 + vecMulVec (y - Pi.single (Fin.natAdd n i) 1) (Pi.single (Fin.natAdd n i) 1) ∧
      toK L (n + r) γ = qel L (n + r) π hπ.ne_zero * toK L (n + r) c * G := by
  have hmax : (Ideal.span {π}).IsMaximal :=
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ).isMaximal
      (by simpa [Ideal.span_singleton_eq_bot] using hπ.ne_zero)
  obtain ⟨u, j0, hj0, hu⟩ := hmax.exists_inv hi
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hj0
  obtain ⟨o, ho⟩ : ∃ o : Fin (n + r), o = ⟨0, by omega⟩ := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Fin (n + r), p = Fin.natAdd n i := ⟨_, rfl⟩
  rw [← ho, ← hp] at hu
  rw [← hp]
  set alg := algebraMap (𝓞 L) L with halg
  have hπL : alg π ≠ 0 := (map_ne_zero_iff _ aff_alg_inj).mpr hπ.ne_zero
  set cL : Matrix (Fin (n + r)) (Fin (n + r)) L := (toK L (n + r) c : Matrix (Fin (n + r)) (Fin (n + r)) L) with hcL
  set ciL : Matrix (Fin (n + r)) (Fin (n + r)) L := (toK L (n + r) c⁻¹ : Matrix (Fin (n + r)) (Fin (n + r)) L) with hciL
  set e : Fin (n + r) → L := Pi.single p 1 with he
  set vL : Fin (n + r) → L := ciL *ᵥ Pi.single o 1 with hvL
  set y : Fin (n + r) → L := ((alg π)⁻¹ * alg u) • vL + alg s • e with hy
  have hcci : cL * ciL = 1 := by
    rw [hcL, hciL, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hvp : vL p = alg (((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) p o) := by
    rw [hvL, Matrix.mulVec_single_one]; rfl
  have hyp : y p = (alg π)⁻¹ := by
    have h := congrArg alg hu
    simp only [map_add, map_mul, map_one] at h
    rw [hy, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hvp, he, Pi.single_eq_same, smul_eq_mul, smul_eq_mul]
    field_simp
    try linear_combination h
  have hdet : (1 + vecMulVec (y - e) e).det ≠ 0 := by
    have h1 : vecMulVec (y - e) e = replicateCol Unit (y - e) * replicateRow Unit e := by
      ext a b; simp [vecMulVec_apply, Matrix.mul_apply]
    rw [h1, det_one_add_replicateCol_mul_replicateRow]
    have h2 : e ⬝ᵥ (y - e) = y p - 1 := by
      simp [he, dotProduct, Pi.single_apply]
    rw [h2, hyp]; simp [hπL]
  refine ⟨y, GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩

  set qO : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) := diagonal fun a => if (a : ℕ) = 0 then π else 1 with hqO
  set eO : Fin (n + r) → 𝓞 L := Pi.single p 1 with heO
  set zO : Fin (n + r) → 𝓞 L := Pi.single o u + (s - 1) • ((qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))) *ᵥ eO) with hzO
  set γM : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) := qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) + vecMulVec zO eO with hγM
  have hqM : ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) = qO.map alg := by
    rw [hqO, Matrix.diagonal_map (map_zero _)]
    show diagonal _ = _
    congr 1
    funext a
    split_ifs <;> first | rfl | simp
  have hQ : (qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))).map alg =
      ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL := by
    rw [Matrix.map_mul, hqM]; rfl
  have he' : (fun a => alg (eO a)) = e := by
    funext a; rw [heO, he, Pi.single_apply, Pi.single_apply]; split_ifs <;> simp
  have h1 : cL *ᵥ vL = Pi.single o 1 := by rw [hvL, Matrix.mulVec_mulVec, hcci, Matrix.one_mulVec]
  have h2 : cL *ᵥ y = ((alg π)⁻¹ * alg u) • Pi.single o 1 + alg s • (cL *ᵥ e) := by
    rw [hy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1]
  have h3 : ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) *ᵥ Pi.single o (1 : L) =
      Pi.single o (alg π) := by
    rw [hqM, hqO, Matrix.diagonal_map (map_zero _), diagonal_mulVec_single]
    congr 1
    simp [ho]
  have h4 : (((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL) *ᵥ (y - e) =
      fun a => alg (zO a) := by
    rw [Matrix.mulVec_sub, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h3,
      Matrix.mulVec_mulVec]
    funext a
    have h5 : alg (((qO * (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))) *ᵥ eO) a) =
        ((((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL) *ᵥ e) a := by
      rw [RingHom.map_mulVec, hQ]
      congr 1
      try exact he'
    rw [hzO, Pi.add_apply, Pi.smul_apply, map_add, smul_eq_mul, map_mul, h5, map_sub, map_one]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply]
    split_ifs
    · field_simp
      try ring
    · simp
      try ring
  have hγdet : IsUnit γM.det := by
    have h6 : γM.map alg = ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL *
        (1 + vecMulVec (y - e) e) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, h4, hγM, Matrix.map_add _ (map_add alg), hQ]
      congr 1
      ext a b
      simp only [Matrix.map_apply, vecMulVec_apply, map_mul]
      rw [← he']
    have h7 : alg γM.det = alg (c : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)).det := by
      rw [RingHom.map_det, RingHom.map_det]
      show (γM.map alg).det = (cL).det
      rw [h6, Matrix.det_mul, Matrix.det_mul, hqM, hqO, Matrix.diagonal_map (map_zero _), Matrix.det_diagonal]
      have h8 : (1 + vecMulVec (y - e) e).det = (alg π)⁻¹ := by
        have h1 : vecMulVec (y - e) e = replicateCol Unit (y - e) * replicateRow Unit e := by
          ext a b; simp [vecMulVec_apply, Matrix.mul_apply]
        rw [h1, det_one_add_replicateCol_mul_replicateRow]
        have h2 : e ⬝ᵥ (y - e) = y p - 1 := by
          simp [he, dotProduct, Pi.single_apply]
        rw [h2, hyp]; ring
      rw [h8, Finset.prod_eq_single o]
      · simp [ho]
        field_simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext (by rw [h, ho]))
        simp [this]
      · simp
    rw [aff_alg_inj h7]
    exact (Matrix.isUnits_det_units c)
  refine ⟨GeneralLinearGroup.mk'' γM hγdet, rfl, ?_⟩
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  rw [aff_toK_val]
  have h6 : γM.map alg = ((qel L (n + r) π hπ.ne_zero : GK L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) L) * cL *
      (1 + vecMulVec (y - e) e) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, h4, hγM, Matrix.map_add _ (map_add alg), hQ]
    congr 1
    ext a b
    simp only [Matrix.map_apply, vecMulVec_apply, map_mul]
    rw [← he']
  have h9 := congrArg (fun M => M a b) h6
  simp only [Matrix.map_apply] at h9
  exact h9

end Gamma

theorem aff_blk_top {K : Type} [Field K] (n r : ℕ) (i : Fin r) (h : GL (Fin n) K) (y : Fin (n + r) → K)
    (a b : Fin n) :
    (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) +
        vecMulVec (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
          (Pi.single (Fin.natAdd n i) 1) : Matrix (Fin (n + r)) (Fin (n + r)) K)) (Fin.castAdd r a) (Fin.castAdd r b) = (h : Matrix (Fin n) (Fin n) K) a b := by
  have hne : Fin.castAdd r b ≠ Fin.natAdd n i := by
    intro hh
    have := congrArg Fin.val hh
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  rw [Matrix.add_apply, vecMulVec_apply, Pi.single_apply, if_neg hne, mul_zero, add_zero, aff_stab_top]

theorem aff_blk_low {K : Type} [Field K] (n r : ℕ) (i : Fin r) (h : GL (Fin n) K) (y : Fin (n + r) → K)
    (a : Fin r) (b : Fin (n + r)) :
    (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) +
        vecMulVec (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
          (Pi.single (Fin.natAdd n i) 1) : Matrix (Fin (n + r)) (Fin (n + r)) K)) (Fin.natAdd n a) b =
      (1 : Matrix (Fin (n + r)) (Fin (n + r)) K) (Fin.natAdd n a) b := by
  have h0 : (((stab K n (n + r) (Nat.le_add_right n r) h : Matrix (Fin (n + r)) (Fin (n + r)) K) - 1) *ᵥ y)
      (Fin.natAdd n a) = 0 := by
    simp [mulVec, dotProduct, Matrix.sub_apply, aff_stab_low]
  rw [Matrix.add_apply, vecMulVec_apply, h0, zero_mul, add_zero, aff_stab_low]

theorem pStabVan : PStabVan := by
  intro _hCh hEv hAff L _ _ hC k hk π hπ n r hn _hr c ⟨i, hi⟩ F hF hdF H hH w hw
  obtain ⟨y, G, γ, hG, hγ⟩ := aff_gamma π hπ n r hn c i hi
  set q := qel L (n + r) π hπ.ne_zero with hq
  have hex : ∀ h : H, ∃ x : Gm L (n + r), toK L (n + r) x =
      G⁻¹ * toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (h : Gm L n)) * G := by
    intro h
    obtain ⟨_, ⟨δ, rfl⟩, hx⟩ := hH h h.2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hx
    refine ⟨γ⁻¹ * δ * γ, ?_⟩
    have hδ : toK L (n + r) δ =
        q * toK L (n + r) (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (h : Gm L n) * c⁻¹) * q⁻¹ := by
      rw [← hx]; group
    rw [map_mul, map_mul, map_inv, hγ, hδ, map_mul, map_mul, map_inv]
    group
  choose fx hfx using hex
  let f : H →* Gm L (n + r) := MonoidHom.mk' fx (fun a b => aff_toK_inj _ (by
    rw [map_mul, hfx, hfx, hfx, Subgroup.coe_mul, map_mul, map_mul]
    group))
  have hf : ∀ h : H, toK L (n + r) (f h) =
      G⁻¹ * toK L (n + r) (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (h : Gm L n)) * G := hfx
  have hM : ∀ h : H, (toK L (n + r) (f h) : Matrix (Fin (n + r)) (Fin (n + r)) L) =
      (stab L n (n + r) (Nat.le_add_right n r) (toK L n h) : Matrix (Fin (n + r)) (Fin (n + r)) L) +
        vecMulVec (((stab L n (n + r) (Nat.le_add_right n r) (toK L n h) : Matrix (Fin (n + r)) (Fin (n + r)) L) - 1)
          *ᵥ y) (Pi.single (Fin.natAdd n i) 1) := by
    intro h
    rw [hf, aff_toK_stab]
    exact aff_conj n r i (toK L n h) y G hG
  have hblock : ∀ x : H, ∃ B : Matrix (Fin n) (Fin r) (𝓞 L),
      (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (H.subtype x : Matrix (Fin n) (Fin n) (𝓞 L)) B 0 1) := by
    intro x
    refine ⟨fun a b => (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.castAdd r a) (Fin.natAdd n b), ?_⟩
    refine Matrix.ext fun a b => ?_
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rcases a with a | a <;> rcases b with b | b
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁]
      apply aff_alg_inj
      rw [← aff_toK_val, hM, aff_blk_top]
      rfl
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      rfl
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      show (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n a) (Fin.castAdd r b) = 0
      apply aff_alg_inj
      rw [map_zero, ← aff_toK_val, hM, aff_blk_low, Matrix.one_apply, if_neg]
      intro hh
      have := congrArg Fin.val hh
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      show (f x : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) (Fin.natAdd n a) (Fin.natAdd n b) =
        (1 : Matrix (Fin r) (Fin r) (𝓞 L)) a b
      apply aff_alg_inj
      rw [← aff_toK_val, hM, aff_blk_low, Matrix.one_apply, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, if_neg (fun hh => hab (Fin.ext (by
        have := congrArg Fin.val hh; simp only [Fin.val_natAdd] at this; omega))), map_zero]
  have key : ∀ h : H, q * toK L (n + r) (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) ((h : Gm L n) * 1)) =
      toK L (n + r) γ • ((toK L (n + r)).comp f h • G⁻¹) := by
    intro h
    rw [smul_eq_mul, smul_eq_mul, MonoidHom.comp_apply, hf, hγ, mul_one, map_mul]
    group
  have hL : ev H.subtype (fun y => F fun j => q * toK L (n + r)
      (c * stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (y j))) 1 w =
      ev ((toK L (n + r)).comp f) F G⁻¹ w := by
    unfold ev
    refine Finsupp.sum_congr fun x _ => ?_
    congr 1
    rw [← hF γ (fun j => (toK L (n + r)).comp f (Fin.partialProd x j) • G⁻¹)]
    exact congrArg F (funext fun j => key (Fin.partialProd x j))
  have hR : ev H.subtype (fun y => F fun j => toK L (n + r)
      (stab (𝓞 L) n (n + r) (Nat.le_add_right n r) (y j))) 1 w =
      ev (toK L (n + r)) F 1 (cmap ((stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp H.subtype) (k + 1) w) := by
    rw [ev_cmap]
    unfold ev
    refine Finsupp.sum_congr fun x _ => ?_
    simp only [MonoidHom.comp_apply, smul_eq_mul, mul_one]
  have hE1 := hEv H (GK L (n + r)) (GK L (n + r)) ((toK L (n + r)).comp f) k F (fun g y => hF (f g) y) hdF
  have hE2 := hEv (Gm L (n + r)) (GK L (n + r)) (GK L (n + r)) (toK L (n + r)) k F hF hdF
  have hbd := hAff L hC k hk n r H f H.subtype hblock w hw
  rw [hL, hR, hE1.2 G⁻¹ 1 w hw, ← ev_cmap]
  have h0 := hE2.1 1 _ hbd
  rw [ev_sub] at h0
  linarith

end PositivityTheory.KB.AffineStabilizerVanishing

end
end

section
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.AffineStabilizerVanishing

open PositivityTheory.KB

theorem pKey (hT : PTransfer) : PKey := by
  intro hCh hEv hAff L _ _ hC k hk π hπ n r hn1 hr1 F hFinv hFcoc z hz
  haveI := (pIndex L (n + r) π hπ).1
  haveI := (pIndex L n π hπ).1
  have hSK := pStabK L π hπ.ne_zero n r hn1
  refine keyGen hT hSK.1 hSK.2 (fun c => pGqStab L π hπ n r hn1 c) k F hFinv hFcoc ?_ z hz
  intro c hc H hH w hw
  have hlow : ∃ i : Fin r, ((c⁻¹ : Gm L (n + r)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L))
      (Fin.natAdd n i) ⟨0, by omega⟩ ∉ Ideal.span {π} := by
    by_contra hne
    push_neg at hne
    obtain ⟨c', hc'⟩ := pLow L π hπ n r hn1 c hne
    exact hc c' hc'
  have h := pStabVan hCh hEv hAff L hC k hk π hπ n r hn1 hr1 c hlow F hFinv hFcoc H hH w hw
  simpa only [map_mul, mul_assoc] using h

end PositivityTheory.KB.AffineStabilizerVanishing

end
end
