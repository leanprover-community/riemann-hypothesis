import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.DivPowInteg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem expS_zero' {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  rw [PowerSeries.subst_zero_eq_C_constantCoeff]
  simp

theorem cc_expS {n : ℕ} (F : PS k n d) (hF : constantCoeff F = 0) : constantCoeff (FB.expS k F) = 1 := by
  have ha : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF
  have h1 : PowerSeries.exp k = 1 + (PowerSeries.exp k - 1) := by ring
  have h2 : PowerSeries.constantCoeff (PowerSeries.exp k - 1) = 0 := by simp
  unfold FB.expS
  rw [h1, ← PowerSeries.coe_substAlgHom ha, map_add, map_one, map_add, PowerSeries.coe_substAlgHom ha,
    PowerSeries.constantCoeff_subst_eq_zero hF _ h2, map_one, add_zero]

def embX (d : ℕ) : Fin 1 × Fin d ↪ Fin d ⊕ Fin d :=
  ⟨fun p => Sum.inl p.2, fun p q hpq => by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, j⟩ := q
    simp only [Sum.inl.injEq] at hpq
    rw [Subsingleton.elim a b, hpq]⟩

theorem liftX_eq_rename (f : PS k 1 d) : liftX k f = rename (embX d) f := by
  rw [MvPowerSeries.rename_eq_subst]
  rfl

theorem cc_liftX (f : PS k 1 d) : constantCoeff (liftX k f) = constantCoeff f := by
  rw [liftX_eq_rename, MvPowerSeries.constantCoeff_rename]

theorem intAA_liftX (f : PS k 1 d) (hf : IntAA (R := R) k f) : IntAA (R := R) k (liftX k f) := by
  rw [liftX_eq_rename]
  intro n
  rw [MvPowerSeries.coeff_rename]
  exact Subring.sum_mem _ fun u _ => hf u

def GoodE (R : Type) [CommRing R] [Algebra R k] (E0 X : AA k d) : Prop :=
  ∃ G : AA k d, IntAA (R := R) k G ∧ X = E0 * G

theorem good_pow (E0 : AA k d) (T : Module.End k (AA k d)) (hT : ∀ X, GoodE R E0 X → GoodE R E0 (T X))
    (n : ℕ) : ∀ X, GoodE R E0 X → GoodE R E0 ((T ^ n) X) := by
  induction n with
  | zero =>
    intro X hX
    rw [pow_zero]
    exact hX
  | succ n ih =>
    intro X hX
    rw [pow_succ]
    exact ih (T X) (hT X hX)

theorem good_prod (E0 : AA k d) (L : List (Module.End k (AA k d)))
    (hL : ∀ T ∈ L, ∀ X, GoodE R E0 X → GoodE R E0 (T X)) : ∀ X, GoodE R E0 X → GoodE R E0 (L.prod X) := by
  induction L with
  | nil =>
    intro X hX
    rw [List.prod_nil]
    exact hX
  | cons T L ih =>
    intro X hX
    rw [List.prod_cons]
    exact hL T (by simp) _ (ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) X hX)

theorem good_ofFn (E0 : AA k d) {r : ℕ} (a : Fin r → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (e : Fin r → ℕ) :
    ∀ X, GoodE R E0 X → GoodE R E0 ((List.ofFn fun i => a i ^ e i).prod X) := by
  refine good_prod E0 _ ?_
  intro T hT
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hT
  exact good_pow E0 (a i) (ha i) (e i)

theorem cc_ordEval_mem (J : Submodule R k) (e : ℕ) (E0 : AA k d) (hE0 : constantCoeff E0 = 1) {r q : ℕ}
    (a : Fin r → Module.End k (AA k d)) (a' : Fin q → Module.End k (AA k d))
    (ha : ∀ i X, GoodE R E0 X → GoodE R E0 (a i X)) (ha' : ∀ j X, GoodE R E0 X → GoodE R E0 (a' j X))
    (σ : AA k d) (hσ : GoodE R E0 σ) (Q : MvPolynomial (Fin r ⊕ Fin q) k) (hQ : ∀ mo, Q.coeff mo ∈ J ^ e) :
    constantCoeff (PI.WickFormula.ordEval a a' Q σ) ∈ J ^ e := by
  unfold PI.WickFormula.ordEval
  rw [LinearMap.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun mo _ => ?_
  have hgood : GoodE R E0 (((List.ofFn fun i => a i ^ mo (Sum.inl i)).prod *
      (List.ofFn fun j => a' j ^ mo (Sum.inr j)).prod) σ) :=
    good_ofFn E0 a ha _ _ (good_ofFn E0 a' ha' _ σ hσ)
  obtain ⟨G, hGi, hGe⟩ := hgood
  rw [LinearMap.smul_apply, hGe, MvPowerSeries.smul_eq_C_mul, map_mul, map_mul,
    MvPowerSeries.constantCoeff_C, hE0, one_mul]
  obtain ⟨r, hr⟩ := hGi 0
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← hr, mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ r (hQ mo)

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem cc_hL (B : FB R d O) (h : PS k 2 d) (hc : B.IsCanonGauge k h) (w0 : O) :
    constantCoeff (B.hL k h w0) = 0 := by
  have h0 : constantCoeff h = 0 := by
    have e := WickVanishing.coeff_ev_zero_left h 0
    rw [hc.ax0, Finsupp.embDomain_zero] at e
    rw [← coeff_zero_eq_constantCoeff_apply, ← e, map_zero]
  unfold FB.hL
  rw [WickVanishing.gt_const_ev_eq _ ?_ h, h0]
  intro j
  fin_cases j
  · exact WickVanishing.gp_pt 0
  · exact WickVanishing.gp_comp1 _ _ (fun i => by simp [FB.actK, B.A.const]) (WickVanishing.gp_pt 0)

theorem sc_of (hN1 : ConnectionIntegrality) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : SCSt := by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hcg w0 hw0 m ι π _ _ _ c s ξh ψ hH hψ h11 h21 h12 P hPint e he f hf
  set x := (m : k) • B.hL k h w0 with hx
  have hx0 : constantCoeff x = 0 := by
    rw [hx, smul_eq_C_mul, map_mul, constantCoeff_C, cc_hL B h hcg w0, mul_zero]
  set E0 := liftX k (FB.expS k x) with hE0def
  set E1 := liftX k (FB.expS k (-x)) with hE1def
  have hE : E0 * E1 = 1 := by
    rw [hE0def, hE1def, ← liftX_mul, ← WickVanishing.gt_expS_add _ _ hx0 (by rw [map_neg, hx0, neg_zero]),
      add_neg_cancel, expS_zero', liftX_eq_rename, map_one]
  have hE0 : constantCoeff E0 = 1 := by rw [hE0def, cc_liftX, cc_expS _ hx0]
  have hgood : ∀ l X, GoodE R E0 X → GoodE R E0 (nablaL B h m (ξh l).1 (ξh l).2 X) := by
    rintro l X ⟨G, hG, rfl⟩
    refine ⟨E1 * nabla k B h m (ξh l).1 (ξh l).2 (E0 * G),
      hN1 R d O k hRQ B h hcg w0 hw0 m (ξh l) (hH l) G hG, ?_⟩
    rw [← mul_assoc, hE, one_mul]
    rfl
  have hσ : GoodE R E0 (liftX k (FB.expS k x * f)) := ⟨liftX k f, intAA_liftX f hf, liftX_mul _ _⟩
  have haa : ∀ l l', s l = s l' → betaH k (ξh l) (ξh l') = 0 := fun l l' e' => h11 l l' fun hh => hh.2 e'
  have hab : ∀ l l', s l = s l' → betaH k (ξh l) (0, ψ l') = 0 := fun l l' e' => h12 l l' fun hh => hh.2 e'
  have hκ : ∀ l l', kapW m s ξh (fun l => (0, ψ l)) l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false := by
    intro l l' hne
    obtain ⟨hs, hs'⟩ := kapW_supp m s ξh _ l l' hne
    refine ⟨?_, hs, hs'⟩
    by_contra hc
    apply hne
    unfold kapW
    rw [if_pos ⟨hs, hs'⟩, h21 l l' (fun hh => hc hh.1), mul_zero]
  have hκJ : ∀ i j, kapE s (kapW m s ξh (fun l => (0, ψ l))) i j ∈ J := by
    intro i j
    unfold kapE kapW
    split_ifs
    · obtain ⟨u, φ, hu⟩ := hH ((sideE s).symm (Sum.inr j))
      rw [hu]
      unfold betaH
      simp only [Pi.zero_apply, mul_zero, zero_sub]
      rw [← nsmul_eq_mul]
      refine J.toAddSubmonoid.nsmul_mem (J.sum_mem fun t _ => J.neg_mem ?_) m
      rw [mul_comm, ← Algebra.smul_def]
      exact J.smul_mem _ (hψ _ t)
    · exact J.zero_mem
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (MvPolynomial.map (algebraMap R k)) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr fun a ha => ?_
    obtain ⟨n', _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    exact RingHom.mem_range.mp (hPint n')
  rw [ordNabla_wick hN2 hN3 B h m s ξh (fun l => (0, ψ l)) (fun _ => rfl) haa hab P (FB.expS k x * f), map_sum]
  refine Submodule.sum_mem _ fun n _ => ?_
  refine cc_ordEval_mem J e E0 hE0 (opL B h m s ξh) (opR B h m s ξh) (fun i => hgood _) (fun j => hgood _) _ hσ _
    fun mo => ?_
  by_cases hne : n ≤ e
  · refine pow_le_pow_right' (Submodule.one_le.mpr hJ1) hne ?_
    have key := (_root_.divided_power_integrality R k _ _ J _ hκJ (MvPolynomial.rename (sideE s) P0) n).1 mo
    rw [← delta_pow_rename s _ (kapW_supp m s ξh _) n P, ← hP0, ← MvPolynomial.map_rename]
    exact key
  · rw [secondOrder_iterate_eq_zero c s _ hκ P e he n (by omega), map_zero, smul_zero, MvPolynomial.coeff_zero]
    exact Submodule.zero_mem _

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end
