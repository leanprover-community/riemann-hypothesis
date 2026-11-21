import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite

section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_lattice_approx_mod_n_completedLattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (n : ℕ), 0 < n → n.Coprime p → ∀ a : D.La, ∃ u ∈ X.lat, ∃ e ∈ LaHat D, X.r u = inAf D a + n • e := by
  intro p hp D X n hn hnp a
  obtain ⟨w, e₀, he₀, h⟩ := X.dense n hn (inAf D a)
  rw [← X.r_apply] at h
  have hrw : X.r w ∈ LaHat D := by
    have h2 : X.r w = inAf D a - n • e₀ := eq_sub_of_add_eq h.symm
    rw [h2]
    exact sub_mem (GlobalTheory.LKGeo.DenEnd.inAf_mem D a) (AddSubgroup.nsmul_mem _ he₀ n)
  obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
  have hphi : 0 < Nat.totient n := Nat.totient_pos.2 hn
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hmod : (p ^ Nat.totient n) ^ k ≡ 1 [MOD n] := by
    simpa using (Nat.ModEq.pow_totient hnp.symm).pow k
  have hle : k ≤ Nat.totient n * k := Nat.le_mul_of_pos_left k hphi
  have ht1 : 1 ≤ p ^ (Nat.totient n * k) := Nat.one_le_pow _ _ hp0
  obtain ⟨q, hq⟩ : n ∣ p ^ (Nat.totient n * k) - 1 :=
    (Nat.modEq_iff_dvd' ht1).1 (by rw [pow_mul]; exact hmod.symm)
  have ht : p ^ (Nat.totient n * k) = 1 + n * q := by omega
  have hM : p ^ (Nat.totient n * k) • w ∈ X.M := by
    have h3 : p ^ (Nat.totient n * k) = p ^ (Nat.totient n * k - k) * p ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [h3, mul_smul]
    exact AddSubgroup.nsmul_mem _ hk _
  have hr : X.r (p ^ (Nat.totient n * k) • w) = inAf D a + n • (q • X.r w - e₀) := by
    rw [map_nsmul, ht, add_smul, one_smul, mul_smul, smul_sub, h]
    generalize n • q • X.r w = y
    generalize n • e₀ = z
    abel
  refine ⟨p ^ (Nat.totient n * k) • w, ?_, q • X.r w - e₀, ?_, hr⟩
  · refine X.mem_lat.2 ⟨hM, ?_⟩
    rw [hr]
    exact add_mem (GlobalTheory.LKGeo.DenEnd.inAf_mem D a)
      (AddSubgroup.nsmul_mem _ (sub_mem (AddSubgroup.nsmul_mem _ hrw q) he₀) n)
  · exact sub_mem (AddSubgroup.nsmul_mem _ hrw q) he₀
end

section
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_lattice_lift_congr_mod_coprime :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), ∃ f : ℕ → D.La →+ X.lat, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a : D.La, ∃ e ∈ LaHat D, X.r (f n a : VQ D) = inAf D a + n • e := by
  intro p _ D X
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  have key : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a : D.La,
      ∃ u ∈ X.lat, ∃ e ∈ LaHat D, X.r u = inAf D a + n • e :=
    fun n hn hc a => UpperTheory.exists_lattice_approx_mod_n_completedLattice p D X n hn hc a
  let g : ℕ → Module.Free.ChooseBasisIndex ℤ D.La → X.lat := fun n i =>
    if h : 0 < n ∧ n.Coprime p then
      ⟨(key n h.1 h.2 (b i)).choose, (key n h.1 h.2 (b i)).choose_spec.1⟩
    else 0
  refine ⟨fun n => (b.constr ℤ (g n)).toAddMonoidHom, ?_⟩
  intro n hn hc a
  let φ : D.La →+ AfP p ⊗[ℚ] VQ D :=
    ((X.r.toAddMonoidHom.comp X.lat.subtype).comp (b.constr ℤ (g n)).toAddMonoidHom)
      - AdelicSim.inAfHom D
  let H : AddSubgroup (AfP p ⊗[ℚ] VQ D) := (LaHat D).map (nsmulAddMonoidHom n)
  have hb : ∀ i, b i ∈ H.comap φ := by
    intro i
    obtain ⟨e, he, heq⟩ := (key n hn hc (b i)).choose_spec.2
    refine AddSubgroup.mem_comap.mpr (AddSubgroup.mem_map.mpr ⟨e, he, ?_⟩)
    have hg : g n i = ⟨(key n hn hc (b i)).choose, (key n hn hc (b i)).choose_spec.1⟩ :=
      dif_pos ⟨hn, hc⟩
    simp only [φ, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      Module.Basis.constr_basis, hg, AddSubgroup.coe_subtype, nsmulAddMonoidHom_apply]
    rw [heq, ← AdelicSim.inAf_eq]
    abel
  have htop : H.comap φ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
      rw [b.span_eq]; trivial
    rw [Submodule.span_int_eq_addSubgroupClosure] at hx
    exact (AddSubgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hb i) hx
  have ha : a ∈ H.comap φ := htop ▸ AddSubgroup.mem_top a
  obtain ⟨e, he, heq⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_comap.mp ha)
  refine ⟨e, he, ?_⟩
  simp only [φ, nsmulAddMonoidHom_apply, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
    LinearMap.toAddMonoidHom_coe, AddSubgroup.coe_subtype] at heq
  rw [AdelicSim.inAf_eq, heq]
  abel
end
