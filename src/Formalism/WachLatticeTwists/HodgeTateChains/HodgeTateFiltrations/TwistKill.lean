import Formalism.WachLatticeTwists.HodgeTateChains.XiAdicFiltrationData
import Formalism.WachLatticeTwists.HodgeTateChains.InvariantsCohomologyData
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained
import Formalism.GaloisCohomology.GaloisCohomologyProofs.DevTorsion

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem t2 : InjectivityOnLayerOfPower := by
  intro R _ Xm _ _ g k z α h hz
  have e1 : (g - 1) * (∑ j ∈ Finset.range k, g ^ j) = g ^ k - 1 := mul_geom_sum g k
  have e2 : (∑ j ∈ Finset.range k, g ^ j) * (g - 1) = g ^ k - 1 := geom_sum_mul g k
  constructor
  · intro x hx
    have h1 : (g ^ k - 1) x = 0 := by
      rw [← e2, Module.End.mul_apply]
      simp [hx]
    have h2 : z • α x = 0 := by
      rw [← h x]; simpa using h1
    exact α.map_eq_zero_iff.1 (hz _ h2)
  · intro x
    refine ⟨(∑ j ∈ Finset.range k, g ^ j) (α.symm x), ?_⟩
    have h1 : (g ^ k - 1) (α.symm x) = z • x := by
      have := h (α.symm x)
      simpa using this
    rw [← h1, ← e1, Module.End.mul_apply]
    simp

section padic

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma tf_pow {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V]
    (htf : ∀ x : V, (ℓ : ℤ_[ℓ]) • x = 0 → x = 0) (k : ℕ) (x : V)
    (h : ((ℓ : ℤ_[ℓ]) ^ k) • x = 0) : x = 0 := by
  induction k with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply htf
    rw [smul_smul, ← pow_succ']
    exact h

lemma unit_of_not_dvd {d : ℕ} (h : ¬ ℓ ∣ d) : IsUnit (d : ℤ_[ℓ]) := by
  rw [PadicInt.isUnit_iff]
  apply le_antisymm (PadicInt.norm_le_one _)
  by_contra hc
  push Not at hc
  have h1 : ‖((d : ℤ) : ℤ_[ℓ])‖ < 1 := by simpa using hc
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h1
  exact h (by exact_mod_cast h1)

lemma index_smul_mem {A : Type} [AddCommGroup A] [Module ℤ_[ℓ] A] (S : Submodule ℤ_[ℓ] A) (d : ℕ)
    (hd : d ≠ 0) (x : A) (h : d • x ∈ S) : ((ℓ : ℤ_[ℓ]) ^ padicValNat ℓ d) • x ∈ S := by
  obtain ⟨d', hd'⟩ := pow_padicValNat_dvd (p := ℓ) (n := d)
  have hnd : ¬ ℓ ∣ d' := by
    intro ⟨t, ht⟩
    apply pow_succ_padicValNat_not_dvd (p := ℓ) hd
    refine ⟨t, ?_⟩
    rw [pow_succ, mul_assoc, ← ht]
    exact hd'
  obtain ⟨c, hc⟩ := unit_of_not_dvd hnd
  have h1 : d • x = (c : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ padicValNat ℓ d) • x) := by
    rw [smul_smul, hc, ← Nat.cast_smul_eq_nsmul ℤ_[ℓ] d x]
    congr 1
    conv_lhs => rw [hd']
    push_cast
    ring
  have h2 : ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (d • x) ∈ S := S.smul_mem _ h
  rw [h1, smul_smul, Units.inv_mul, one_smul] at h2
  exact h2

lemma poly_split (R : Polynomial ℤ_[ℓ]) : ∃ R' : Polynomial ℤ_[ℓ], R = C (R.eval 1) + (X - 1) * R' := by
  obtain ⟨R', hR'⟩ : (X - C (1 : ℤ_[ℓ])) ∣ R - C (R.eval 1) := X_sub_C_dvd_sub_C_eval
  refine ⟨R', ?_⟩
  rw [map_one] at hR'
  rw [← hR']; ring

lemma aeval_split {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V)
    (R R' : Polynomial ℤ_[ℓ]) (h : R = C (R.eval 1) + (X - 1) * R') (x : V) :
    aeval g R x = (R.eval 1) • x + (g (aeval g R' x) - aeval g R' x) := by
  conv_lhs => rw [h]
  simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]

lemma aeval_split' {V : Type} [AddCommGroup V] [Module ℤ_[ℓ] V] (g : V →ₗ[ℤ_[ℓ]] V)
    (R R' : Polynomial ℤ_[ℓ]) (h : R = C (R.eval 1) + (X - 1) * R') (x : V) :
    aeval g R x = (R.eval 1) • x + aeval g R' (g x - x) := by
  conv_lhs => rw [h, mul_comm]
  simp [Module.End.mul_apply, Algebra.algebraMap_eq_smul_one]

end padic

theorem eigen : StatEigen := by
  intro ℓ _ w m hm h2 hw U i V _ _ g htf hkill k x x' hx
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  have h1 : aeval g (Rpoly ℓ w U i) (g x' - x') = 0 := by
    have h0 : aeval g ((X - 1) * Rpoly ℓ w U i) x' = 0 := by rw [hkill]; rfl
    rw [mul_comm, map_mul, Module.End.mul_apply] at h0
    simpa using h0
  have h3 : aeval g (Rpoly ℓ w U i) x = 0 := by
    apply tf_pow htf k
    rw [← map_smul, hx, h1]
  obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
  have h4 := aeval_split g _ R' hR' x
  rw [h3] at h4
  have hu := PadicInt.unitCoeff_spec hne
  rw [hval] at hu
  set c := PadicInt.unitCoeff hne with hc
  refine ⟨-(((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • aeval g R' x), ?_⟩
  have h5 : ((Rpoly ℓ w U i).eval 1) • x = -(g (aeval g R' x) - aeval g R' x) :=
    eq_neg_of_add_eq_zero_left h4.symm
  have h6 : ((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x
      = ((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((Rpoly ℓ w U i).eval 1) • x) := by
    rw [smul_smul]
    conv_rhs => rw [hu, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h6, h5]
  simp only [map_neg, map_smul, smul_neg, smul_sub]
  abel

theorem htpoly : StatHTpoly := by
  intro ℓ _ w U i
  by_cases hi : i ∈ U
  · refine ⟨?_, fun h => absurd hi h⟩
    have : HTpoly ℓ w U i = (X - 1) * Rpoly ℓ w U i := by
      unfold HTpoly Rpoly
      rw [← Finset.mul_prod_erase U _ hi]
      simp
    rw [this]
  · have : HTpoly ℓ w U i = Rpoly ℓ w U i := by
      unfold HTpoly Rpoly
      rw [Finset.erase_eq_of_notMem hi]
    exact ⟨this ▸ dvd_mul_left _ _, fun _ => this⟩

theorem eigenInj : StatEigenInj := by
  intro ℓ _ w m hm h2 hw U i hi V _ _ g htf hkill x hx
  obtain ⟨hne, hval⟩ := rVal ℓ w m hm h2 hw U i
  rw [(htpoly ℓ w U i).2 hi] at hkill
  obtain ⟨R', hR'⟩ := poly_split (Rpoly ℓ w U i)
  have h4 := aeval_split' g _ R' hR' x
  rw [hkill, hx, sub_self, map_zero, add_zero] at h4
  have hu := PadicInt.unitCoeff_spec hne
  rw [hval] at hu
  apply tf_pow htf (rI ℓ m U i)
  have h5 : ((PadicInt.unitCoeff hne : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • (((ℓ : ℤ_[ℓ]) ^ rI ℓ m U i) • x) = 0 := by
    rw [smul_smul, ← hu]; exact h4.symm
  have h6 := congrArg (fun y => (((PadicInt.unitCoeff hne)⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • y) h5
  simpa [smul_smul] using h6

theorem devSum : StatDevSum := by
  intro ℓ _ H Gr _ _ _ _ f p c h0 hex hker hGr n
  induction n with
  | zero => intro x _; rw [h0 x, smul_zero]
  | succ n ih =>
    intro x hx
    rw [Finset.sum_range_succ, add_comm (∑ k ∈ Finset.range n, c k) (c n)]
    exact Formalism.GaloisCohomology.devTorsion ℤ_[ℓ] (Gr n) (H (n + 1)) (H n) (f n) (p n) (ℓ : ℤ_[ℓ]) (c n) _
      (hex n) (hker n) (hGr n) ih x hx

theorem killSum : StatKillSum := by
  intro ℓ _ H Gr _ _ _ _ f p c n h0
  induction n with
  | zero => intro _ _ x; rw [h0 x, smul_zero]
  | succ n ih =>
    intro hex hGr x
    have h1 : p n (((ℓ : ℤ_[ℓ]) ^ (∑ k ∈ Finset.range n, c k)) • x) = 0 := by
      rw [map_smul]
      exact ih (fun k hk => hex k (by omega)) (fun k hk => hGr k (by omega)) _
    obtain ⟨y, hy⟩ := (hex n (by omega) _).1 h1
    rw [Finset.sum_range_succ, add_comm (∑ k ∈ Finset.range n, c k) (c n), pow_add, mul_smul, ← hy,
      ← map_smul, hGr n (by omega) y, map_zero]

theorem cores : StatCores := by
  intro ℓ _ A B _ _ _ _ res cor d c hd hcr hB x ⟨k, hk⟩
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c) • res x = 0 := hB _ ⟨k, by rw [← map_smul, hk, map_zero]⟩
  have h2 : d • (((ℓ : ℤ_[ℓ]) ^ c) • x) = 0 := by
    rw [← hcr, map_smul, h1, map_zero]
  have h3 := index_smul_mem (⊥ : Submodule ℤ_[ℓ] A) d hd _ (by simpa using h2)
  rw [pow_add, mul_smul]
  simpa using h3

theorem reindex : StatReindex := by
  intro ℓ m U a n
  unfold cM
  symm
  apply Finset.sum_bij (fun (k : ℕ) _ => a + (k : ℤ))
  · intro k hk
    have := Finset.mem_range.1 hk
    rw [Finset.mem_Ico]; omega
  · intro k1 _ k2 _ h
    simpa using h
  · intro b hb
    rw [Finset.mem_Ico] at hb
    refine ⟨(b - a).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  · intro k _; rfl



theorem lemmaA : StatLemmaA := by
  intro ℓ Bm _ Am T hsat hcl hT hstep x hx
  apply hcl
  intro n
  induction n with
  | zero => exact ⟨0, Am.zero_mem, x, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha, b, hab⟩ := ih
    have hsatn : ∀ (k : ℕ) (y : Bm), (ℓ ^ k) • y ∈ Am → y ∈ Am := by
      intro k
      induction k with
      | zero => intro y hy; simpa using hy
      | succ k ihk =>
        intro y hy
        apply hsat
        apply ihk
        rw [smul_smul, ← pow_succ]; exact hy
    have h1 : (ℓ ^ n) • T b ∈ Am := by
      have : (ℓ ^ n) • T b = T x - T a := by rw [hab, map_add, map_nsmul]; abel
      rw [this]; exact Am.sub_mem hx (hT a ha)
    obtain ⟨a', ha', b', hab'⟩ := hstep b ⟨T b, hsatn n _ h1, 0, by simp⟩
    refine ⟨a + (ℓ ^ n) • a', Am.add_mem ha (Am.nsmul_mem ha' _), b', ?_⟩
    rw [hab, hab', smul_add, smul_smul, ← pow_succ, add_assoc]

theorem inverse_operator_from_injectivity : InverseOperatorFromInjectivity := by
  intro R _ Xm _ _ g z hinj hsur
  choose S hS using hsur
  have huniq : ∀ a b : Xm, g a - a = g b - b → a = b := by
    intro a b h
    have : g (a - b) = a - b := by
      rw [map_sub]
      have h' : g a - g b = a - b := by
        have := sub_eq_sub_iff_add_eq_add.1 h
        rw [sub_eq_sub_iff_add_eq_add, this, add_comm]
      exact h'
    exact sub_eq_zero.1 (hinj _ this)
  refine ⟨{ toFun := S, map_add' := ?_, map_smul' := ?_ }, ?_, ?_⟩
  · intro a b
    apply huniq
    rw [← hS, map_add, smul_add, hS a, hS b]; abel
  · intro c a
    apply huniq
    rw [← hS, RingHom.id_apply, map_smul, ← smul_sub, ← hS a, smul_comm]
  · intro x; exact (hS x).symm
  · intro x
    apply huniq
    show g (S (g x - x)) - S (g x - x) = _
    rw [← hS, map_smul, smul_sub]

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

theorem piece : StatPiece := by
  intro ℓ _ w m hm h2 hw U i A P ⟨hS, ⟨hIR1, hIR2⟩, hT4, ⟨_, hT3⟩, htf, hHT⟩ y ⟨k, hk⟩
  have hkill : aeval P.gm ((X - 1) * Rpoly ℓ w U i) = 0 := by
    obtain ⟨q, hq⟩ := (htpoly ℓ w U i).1
    rw [hq, map_mul, hHT, zero_mul]
  have h1 : P.res ((ℓ : ℤ_[ℓ]) • P.lam y) = 0 := by rw [map_smul]; exact hT4 _
  obtain ⟨a, x, hax⟩ := (hIR1 _).1 h1
  have h3 : P.infm (((ℓ : ℤ_[ℓ]) ^ k) • a) + P.infX (((ℓ : ℤ_[ℓ]) ^ k) • x) = 0 := by
    rw [map_smul, map_smul, ← smul_add, ← hax, smul_comm, ← map_smul, hk, map_zero, smul_zero]
  obtain ⟨⟨a', ha'⟩, _⟩ := (hIR2 _ _).1 h3
  obtain ⟨a'', ha''⟩ := eigen ℓ w m hm h2 hw U i P.Wm P.gm htf hkill k a a' ha'
  obtain ⟨x'', hx''⟩ := hT3 x
  have h4 : P.infm (((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i))) • a) + P.infX (((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i))) • x) = 0 := by
    apply (hIR2 _ _).2
    constructor
    · refine ⟨((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) - rI ℓ m U i)) • a'', ?_⟩
      rw [map_smul, ← smul_sub, ← ha'', smul_smul, ← pow_add, Nat.sub_add_cancel (le_max_right _ _)]
    · refine ⟨((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) - 1)) • x'', ?_⟩
      rw [map_smul, ← smul_sub, ← hx'', smul_smul, ← pow_succ, Nat.sub_add_cancel (le_max_left _ _)]
  have h5 : ((ℓ : ℤ_[ℓ]) ^ (max 1 (rI ℓ m U i) + 1)) • P.lam y = 0 := by
    rw [pow_succ, mul_smul, hax, smul_add, ← map_smul, ← map_smul]; exact h4
  have h6 := congrArg P.io h5
  rw [map_smul, hS, map_zero, smul_smul, ← pow_succ] at h6
  have h7 : 2 + max 1 (rI ℓ m U i) = max 1 (rI ℓ m U i) + 1 + 1 := by ring
  rw [h7]; exact h6

theorem ll : StatLL := by
  intro ℓ _ w m hm h2 hw U a n d D hd hP ⟨h0, hex⟩ hT5 hcr
  have hGr : ∀ k, TorsKilled ℓ (D.Gr k) (2 + max 1 (rI ℓ m U (a + k))) :=
    fun k => piece ℓ w m hm h2 hw U (a + k) (D.Gr k) (D.piece k) (hP k)
  have hm' := devSum ℓ (fun k => D.Hm k) (fun k => D.Gr k) D.f D.p _ h0 hex hT5 hGr n
  rw [← reindex] at hm'
  exact cores ℓ D.HK (D.Hm n) D.res D.cor d _ hd hcr hm'

theorem h0 : InvariantsKilledByPower := by
  intro ℓ _ w m hm h2 hw U h0U hne D hP hUn hFl hLES ⟨hInv1, hInv2⟩ x
  have hA := piece ℓ w m hm h2 hw U 0 D.A D.piece hP
  have hr : rI ℓ m U 0 = ∑ u ∈ U, (m + padicValInt ℓ u) := by
    unfold rI; rw [Finset.erase_eq_of_notMem h0U]; simp
  have hr1 : 1 ≤ rI ℓ m U 0 := by
    rw [hr]
    obtain ⟨u, hu⟩ := hne
    calc 1 ≤ m + padicValInt ℓ u := by omega
      _ ≤ _ := Finset.single_le_sum (f := fun u => m + padicValInt ℓ u) (fun _ _ => Nat.zero_le _) hu
  have hc : 2 + max 1 (rI ℓ m U 0) = c0 ℓ m U := by unfold c0; rw [max_eq_right hr1, hr]
  rw [hc] at hA
  obtain ⟨_, _, _, ⟨hT3inj, _⟩, htf, hHT⟩ := hP
  have hW0 : ∀ z : D.H0WeightInvariants, z = 0 := fun z =>
    hInv1 z (eigenInj ℓ w m hm h2 hw U 0 h0U D.piece.Wm D.piece.gm htf hHT _ (hInv2 z).1)
      (hT3inj _ (hInv2 z).2)
  obtain ⟨r, hr'⟩ := hUn x
  let x' : Submodule.torsionBy ℤ_[ℓ] D.M ((ℓ : ℤ_[ℓ]) ^ r) :=
    ⟨x, by rw [Submodule.mem_torsionBy_iff]; exact hr'⟩
  have hx0 : ((ℓ : ℤ_[ℓ]) ^ r) • x' = 0 := Subtype.ext hr'
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • D.dl r (D.emb r x') = 0 :=
    hA _ ⟨r, by rw [← map_smul, ← map_smul, hx0, map_zero, map_zero]⟩
  have h2' : D.dl r (D.emb r (((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x')) = 0 := by rw [map_smul, map_smul]; exact h1
  obtain ⟨z, hz⟩ := (hLES r _).1 h2'
  rw [hW0 z, map_zero] at hz
  have h3 : ((ℓ : ℤ_[ℓ]) ^ c0 ℓ m U) • x' = 0 := hFl r (by rw [← hz, map_zero])
  exact congrArg Subtype.val h3

theorem tb : StatTB := by
  intro ℓ _ s m e d U D hd ⟨c1, c2, c3, c4, c5, c6, c7⟩ ⟨e1, e2, e3⟩ hdR hLL hH2 hK3 hF3 hR ⟨hcr, hcf⟩
  have hℓ : ℓ.Prime := Fact.out
  have hle := (cTBTable ℓ hℓ s m e (padicValNat ℓ d) U).2
  generalize cTB ℓ s m e (padicValNat ℓ d) U = N at hle ⊢
  generalize cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s)) = c at hle hLL
  unfold TBData.tateDualityKillsH2 at hH2
  generalize s + padicValNat ℓ (e + 1) = t at hle hH2
  obtain ⟨z, hz⟩ := (e1 (((ℓ : ℤ_[ℓ]) ^ t) • D.f1 D.y)).1 (by rw [map_smul]; exact hH2 _)
  have h1 : ((ℓ : ℤ_[ℓ]) ^ c) • D.iY D.y = 0 := hLL _ hdR
  have h2 : D.qL (((ℓ : ℤ_[ℓ]) ^ c) • D.iZ z) = 0 := by
    rw [map_smul, c2, hz, map_smul, c1, smul_comm, ← map_smul, h1, map_zero, smul_zero]
  obtain ⟨w, hw⟩ := (e2 _).1 h2
  have h3 : D.bW w = ((ℓ : ℤ_[ℓ]) ^ c) • D.ex (D.jZ z) := by rw [← c4, hw, map_smul, c3]
  obtain ⟨x, hx⟩ := (e3 (((ℓ : ℤ_[ℓ]) ^ cPrime ℓ s e) • w)).1 (by rw [map_smul]; exact hK3 _)
  have h4 : ((ℓ : ℤ_[ℓ]) ^ (cPrime ℓ s e + 1 + s + ceilE ℓ e)) • D.bW w ∈ D.La0 := by
    have h := hF3 x
    rw [hx, map_smul, smul_smul, ← pow_add] at h
    have hexp : cPrime ℓ s e + 1 + s + ceilE ℓ e = 1 + s + ceilE ℓ e + cPrime ℓ s e := by ring
    rw [hexp]; exact h
  obtain ⟨z1, hz1⟩ := hR (D.bW w) _ (aTB ℓ s e) h4 ((aCount ℓ hℓ s e).2.1).symm
  have h5 : D.ex (((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c)) • D.jZ z - D.jW z1) = 0 := by
    rw [map_sub, map_smul, ← hz1, h3, smul_smul, ← pow_add, sub_self]
  have h6 := hcf _ h5
  have h6' : D.pr (((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c)) • D.jZ z - D.jW z1)
      = ((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c + t)) • D.res D.yK := by
    rw [map_sub, c5, sub_zero, map_smul, ← c6, hz, map_smul, ← c7, smul_smul, ← pow_add]
  rw [h6', map_smul, hcr, smul_comm] at h6
  have h8 := index_smul_mem D.HfK d hd _ h6
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
  have h9 : ((ℓ : ℤ_[ℓ]) ^ N) • D.yK
      = ((ℓ : ℤ_[ℓ]) ^ j) • (((ℓ : ℤ_[ℓ]) ^ padicValNat ℓ d) • (((ℓ : ℤ_[ℓ]) ^ (aTB ℓ s e + c + t)) • D.yK)) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add, hj]
    congr 2
    ring
  rw [h9]
  exact D.HfK.smul_mem _ h8

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
end
end

section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem twistKill : StatTwistKill := by
  intro ℓ _ u s hs h2 hu j hj E T ⟨hI1, hI2⟩ hT4 hT3 y
  obtain ⟨hne, hval⟩ := Formalism.WindowSums.valuation_zpow_sub_one ℓ u s hs h2 hu j hj
  obtain ⟨a, x, hax⟩ := (hI1 ((ℓ : ℤ_[ℓ]) • y)).1 (by rw [map_smul]; exact hT4 _)
  obtain ⟨c, hu'⟩ : ∃ c : ℤ_[ℓ]ˣ, (((u ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1)
      = (c : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j) := by
    have h := PadicInt.unitCoeff_spec hne
    rw [hval] at h
    exact ⟨_, h⟩
  have h4 : T.infm (((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j)) • a) + T.infX (((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j)) • x) = 0 := by
    apply (hI2 _ _).2
    constructor
    · refine ⟨((c⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • a, ?_⟩
      have h5 : ∀ (t : ℤ_[ℓ]) (v : T.Wm), t • v - v = (t - 1) • v := by
        intro t v; rw [sub_smul, one_smul]
      rw [h5, smul_smul]
      conv_rhs => rw [hu', mul_right_comm, Units.mul_inv, one_mul]
    · obtain ⟨x'', hx''⟩ := hT3 x
      refine ⟨((ℓ : ℤ_[ℓ]) ^ (s + padicValInt ℓ j - 1)) • x'', ?_⟩
      rw [map_smul, ← smul_sub, ← hx'', smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega)]
  have h6 : 1 + s + padicValInt ℓ j = (s + padicValInt ℓ j) + 1 := by ring
  rw [h6, pow_succ, mul_smul, hax, smul_add, ← map_smul, ← map_smul]
  exact h4

theorem kill3 : StatKill3 := by
  intro ℓ _ u s hs h2 hu e K ⟨h0, hex, htw⟩ x
  refine killSum ℓ (fun k => K.H k) (fun k => K.Gr k) K.f K.p
    (fun k => 1 + s + padicValNat ℓ (e - k)) e h0 hex (fun k hk y => ?_) x
  obtain ⟨hI, hT4, hT3⟩ := htw k hk
  have h := twistKill ℓ u s hs h2 hu ((k : ℤ) - e) (by omega) (K.Gr k) (K.tw k) hI hT4 hT3 y
  have hv : padicValInt ℓ ((k : ℤ) - e) = padicValNat ℓ (e - k) := by
    unfold padicValInt
    congr 1
    omega
  rw [hv] at h
  exact h

theorem free3 : StatFree3 := by
  intro ℓ _ N G HB T b La0 ⟨hI1, hI2⟩ hT4 hT3 htf hlog x
  obtain ⟨a, y, hay⟩ := (hI1 ((ℓ : ℤ_[ℓ]) • x)).1 (by rw [map_smul]; exact hT4 _)
  obtain ⟨y', hy'⟩ := hT3 y
  have h1 : T.infX ((ℓ : ℤ_[ℓ]) • y) = 0 := by
    have := (hI2 0 ((ℓ : ℤ_[ℓ]) • y)).2 ⟨⟨0, by simp⟩, y', hy'⟩
    rw [map_zero, zero_add] at this
    exact this
  have h2 : b (T.infX y) = 0 := htf _ (by rw [← map_smul, ← map_smul, h1, map_zero])
  have h3 : (ℓ : ℤ_[ℓ]) • b x = b (T.infm a) := by rw [← map_smul, hay, map_add, h2, add_zero]
  rw [add_comm, pow_succ, mul_smul, h3]
  exact hlog a

theorem tbFull : StatTBFull := by
  intro ℓ _ u w s m e d hs h2 hsm hu hw U D L K T φ ψ hd hP hLES hT5 hCR hK hTI hT4 hT3 htf hlog
    hC hL hdR hH2 hR hCor
  have hℓ : ℓ.Prime := Fact.out
  have hLL := ll ℓ w m (by omega) (fun h => le_trans (h2 h) hsm) hw U 0 (e + 1) (ℓ ^ (m - s)) L
    (pow_ne_zero _ hℓ.ne_zero) hP hLES hT5 hCR
  have hcast : (0 : ℤ) + ((e + 1 : ℕ) : ℤ) = (e : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hLL
  have hLL' : TorsKilled ℓ D.HYL (cLL ℓ m U 0 ((e : ℤ) + 1) (ℓ ^ (m - s))) := fun x ⟨k, hk⟩ =>
    φ.injective (by
      rw [map_smul, map_zero]
      exact hLL _ ⟨k, by rw [← map_smul, hk, map_zero]⟩)
  have hK3 : D.Kill3 s e := fun x =>
    ψ.injective (by rw [map_smul, map_zero]; exact kill3 ℓ u s hs h2 hu e K hK _)
  have hF3 : D.Free3 s e := fun x => by
    have h := free3 ℓ (s + ceilE ℓ e) D.HGe D.HB T (D.bW ∘ₗ D.gE) D.La0 hTI hT4 hT3 htf hlog x
    rw [← add_assoc] at h
    exact h
  exact tb ℓ s m e d U D hd hC hL hdR hLL' hH2 hK3 hF3 hR hCor

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
end
end
