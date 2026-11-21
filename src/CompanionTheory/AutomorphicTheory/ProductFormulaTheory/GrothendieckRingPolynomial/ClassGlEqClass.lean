import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleApply
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.BernsteinZelevinsky.TopAdm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CuspidalTwistInjectiveImports
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContragredientProductIrreducibleImports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLengthStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffle
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WordOccursOfSubquotientImports

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckPhiBijection

theorem interleave_perm {T : Type*} {u v w : List T} (h : Zc.Comb.Interleave u v w) : w.Perm (u ++ v) := by
  induction h with
  | nil => exact List.Perm.refl _
  | left _ ih => exact ih.cons _
  | right _ ih => exact (ih.cons _).trans List.perm_middle.symm

theorem shuffle_perm {T : Type*} {us : List (List T)} {w : List T} (h : Zc.Comb.Shuffle us w) :
    w.Perm us.flatten := by
  induction h with
  | nil => exact List.Perm.refl _
  | cons _ hi ih => rw [List.flatten_cons]; exact (interleave_perm hi).trans (ih.append_left _)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_decW (Γ : Segment k) : ((decW Γ : List (IrrGL k)) : Multiset (IrrGL k)) = Γ.ms := by
  rw [decW, Segment.ms, ← Fin.univ_val_map]
  have : (fun i : Fin Γ.len => Γ.term i.rev) = Γ.term ∘ (Fin.revPerm : Equiv.Perm (Fin Γ.len)) := rfl
  rw [this, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL k)) : Multiset (IrrGL k)) = msupp (L : Multiset (Segment k)) := by
  induction L with
  | nil => simp [msupp]
  | cons Γ L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, coe_decW, ← Multiset.cons_coe, msupp, msupp,
      Multiset.cons_bind]

theorem coe_eq_msupp_of_inShW {𝔫 : Multiset (Segment k)} {w : List (IrrGL k)} (h : InShW 𝔫 w) :
    (w : Multiset (IrrGL k)) = msupp 𝔫 := by
  obtain ⟨L, rfl, hL⟩ := h
  rw [Multiset.coe_eq_coe.2 (shuffle_perm hL), coe_flatten_decW]

theorem msupp_eq_of_isL (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) {𝔫 : Multiset (Segment k)}
    {x : IrrGL k} (hx : IsL 𝔫 x.rep) (w : List (IrrGL k)) (hc : ∀ c ∈ w, c.IsCusp) (hw : Wd x.rep w) :
    (w : Multiset (IrrGL k)) = msupp 𝔫 := by
  obtain ⟨h, y, hd, ⟨Δ, hΔ, hL⟩, hcos⟩ := hx
  have h1 : Wd (prodIrr y hd) w := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr y hd) hcos.isSubquotient w hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hj y hd Δ hL w hc h1
  rw [hΔ.1] at h2
  exact coe_eq_msupp_of_inShW h2

theorem wd_of_jmL_eq_one {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    {w : List (IrrGL k)} (h : jmL w π = 1) : Wd π w := by
  unfold jmL at h
  split_ifs at h with hd
  · exact ⟨hd, by rw [h]; exact one_ne_zero⟩
  · exact absurd h zero_ne_one

theorem msupp_seg (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) (hS : JSeg k) (Δ : Segment k)
    {𝔫 : Multiset (Segment k)} (h𝔫 : IsL 𝔫 (IrrGL.rep (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k))) : msupp 𝔫 = Δ.ms := by
  have hc : ∀ c ∈ List.ofFn Δ.term, c.IsCusp := by
    intro c hc
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hc
    exact Δ.isCusp_term a
  have := msupp_eq_of_isL hA hj h𝔫 (List.ofFn Δ.term) hc (wd_of_jmL_eq_one (hS Z hZ Δ).1)
  rw [← this, Segment.ms, Fin.univ_val_map]

theorem seg_eq_of_ms_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Γ Δ : Segment k} (h : Γ.ms = Δ.ms) : Γ = Δ := by
  have hlen : Γ.len = Δ.len := by rw [← Segment.card_ms, h, Segment.card_ms]
  have mem_first : ∀ D : Segment k, D.first ∈ D.ms := fun D =>
    Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, D.len_pos, by simp⟩)
  have hΓ : Γ.first ∈ Δ.ms := by rw [← h]; exact mem_first Γ
  have hΔ : Δ.first ∈ Γ.ms := by rw [h]; exact mem_first Δ
  obtain ⟨a, -, ha⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hΓ)
  obtain ⟨b, -, hb⟩ := Segment.mem_carrier.1 (Segment.mem_ms.1 hΔ)
  have h0 : Δ.first.nu ((a + b : ℕ) : ℂ) = Δ.first.nu ((0 : ℕ) : ℂ) := by
    rw [Nat.cast_zero, IrrGL.nu_zero, Nat.cast_add, ← IrrGL.nu_nu, ha, hb]
  have hab := GlobalTheory.T.cuspidal_twist_injective hA Δ.first Δ.isCusp_first _ _ h0
  have ha0 : a = 0 := by omega
  subst ha0
  refine Segment.ext_first ?_ hlen
  rw [← ha]
  simp

theorem len_lt_of_msupp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} {M : Multiset (Segment k)}
    (hM : msupp M = Δ.ms) (hne : M ≠ {Δ}) : ∀ Γ ∈ M, Γ.len < Δ.len := by
  intro Γ hΓ
  have hle : Γ.ms ≤ Δ.ms := by rw [← hM]; exact Multiset.le_bind M hΓ
  have hcard := Multiset.card_le_card hle
  rw [Segment.card_ms, Segment.card_ms] at hcard
  refine lt_of_le_of_ne hcard fun heq => hne ?_
  have hms : Γ.ms = Δ.ms := Multiset.eq_of_le_of_card_le hle (by rw [Segment.card_ms, Segment.card_ms, heq])
  have hΓΔ := seg_eq_of_ms_eq hA hms
  obtain ⟨M', rfl⟩ := Multiset.exists_cons_of_mem hΓ
  have h2 : msupp M' = 0 := by
    have h3 : Γ.ms + msupp M' = Δ.ms := by rw [← hM, msupp, msupp, Multiset.cons_bind]
    rw [hms] at h3
    simpa using h3
  have h3 : M' = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun Γ' hΓ' => ?_
    have h4 : Γ'.ms ≤ msupp M' := Multiset.le_bind M' hΓ'
    rw [h2, Multiset.le_zero] at h4
    have h5 := congrArg Multiset.card h4
    rw [Segment.card_ms, Multiset.card_zero] at h5
    exact Γ'.len_pos.ne' h5
  rw [h3, hΓΔ, Multiset.cons_zero]

theorem toMultiset_eq_single_iff (s : Segment k →₀ ℕ) (Δ : Segment k) :
    Finsupp.toMultiset s = {Δ} ↔ s = Finsupp.single Δ 1 := by
  classical
  constructor
  · intro h
    calc s = Multiset.toFinsupp (Finsupp.toMultiset s) := (Finsupp.toMultiset_toFinsupp s).symm
      _ = Multiset.toFinsupp (Finsupp.toMultiset (Finsupp.single Δ 1)) := by
          rw [h, Finsupp.toMultiset_single, one_nsmul]
      _ = Finsupp.single Δ 1 := Finsupp.toMultiset_toFinsupp _
  · rintro rfl
    rw [Finsupp.toMultiset_single, one_nsmul]

theorem prod_X_of_map (s : Segment k →₀ ℕ) {h : ℕ} (Γ : Fin h → Segment k)
    (hΓ : Finset.univ.val.map Γ = Finsupp.toMultiset s) :
    ∏ a, (MvPolynomial.X (Γ a) : MvPolynomial (Segment k) ℤ) = MvPolynomial.monomial s 1 := by
  classical
  have h1 : (Finset.univ.val.map fun a => (MvPolynomial.X (Γ a) : MvPolynomial (Segment k) ℤ)) =
      (Finset.univ.val.map Γ).map MvPolynomial.X := by
    rw [Multiset.map_map]; rfl
  rw [Finset.prod_eq_multiset_prod, h1, hΓ, Finset.prod_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset]
  exact MvPolynomial.prod_X_pow_eq_monomial

theorem exists_enum (s : Segment k →₀ ℕ) :
    ∃ (h : ℕ) (Γ : Fin h → Segment k), Finset.univ.val.map Γ = Finsupp.toMultiset s :=
  ⟨(Finsupp.toMultiset s).toList.length, fun a => (Finsupp.toMultiset s).toList.get a, by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]⟩

def Jh (W : List (IrrGL k)) : GrothGL k →+ ℤ where
  toFun := J W
  map_zero' := Finsupp.sum_zero_index
  map_add' _ _ := Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

def ell (Δ : Segment k) : GrothGL k →+ ℤ := ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card • Jh (vWord Δ S)

theorem ell_apply (Δ : Segment k) (a : GrothGL k) :
    ell Δ a = ∑ S ∈ vSets Δ, (-1 : ℤ) ^ S.card * J (vWord Δ S) a := by
  simp only [ell, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  rfl

theorem J_sg (W : List (IrrGL k)) (x : IrrGL k) : J W (sg x) = ((jmL W x.rep).toNat : ℤ) := by
  unfold J sg
  rw [Finsupp.sum_single_index (zero_mul _), one_mul]

theorem vWord_empty (Δ : Segment k) : vWord Δ ∅ = List.ofFn Δ.term := by
  simp [vWord, List.ofFn_eq_map]

theorem cusp_vWord (Δ : Segment k) (S : Finset (Fin Δ.len)) : ∀ w ∈ vWord Δ S, w.IsCusp := by
  intro w hw
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
  exact Δ.isCusp_term a

theorem ell_sg {Δ : Segment k} {x : IrrGL k} (h1 : jmL (List.ofFn Δ.term) x.rep = 1)
    (h0 : ∀ S ∈ vSets Δ, S ≠ ∅ → jmL (vWord Δ S) x.rep = 0) : ell Δ (sg x) = 1 := by
  rw [ell_apply, Finset.sum_eq_single (∅ : Finset (Fin Δ.len))]
  · rw [J_sg, vWord_empty, h1]; simp
  · intro S hS hne; rw [J_sg, h0 S hS hne]; simp
  · intro h; exact absurd (by simp [vSets]) h

open Classical in

theorem ell_prod (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL k) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep) (Δ : Segment k) {h N : ℕ}
    (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N) :
    ell Δ (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)) =
      if Finset.univ.val.map Γ = {Δ} then (-1) ^ (Δ.len - 1) else 0 := by
  have := hAlt Δ h Γ
  rw [ell_apply]
  convert this using 1
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [(hJ (vWord Δ S) N _ (prodIrr (fun a => Lseg (Γ a)) hd) (isSmooth_prodIrr _ hd)
      (GlobalTheory.T.product_irreducible_finite_length hA _ hd)).2,
    GlobalTheory.T.segment_product_jacquet_shuffle_count hA hj Γ (fun a => Lseg (Γ a)) hd (fun i => hL (Γ i)) (vWord Δ S) (cusp_vWord Δ S)]
  simp

theorem vars_lt (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (p : MvPolynomial (Segment k) ℤ)
    (hp : ∀ s ∈ p.support, msupp (Finsupp.toMultiset s) = Δ.ms) :
    ∀ t ∈ (p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1))).vars, t.len < Δ.len := by
  classical
  intro t ht
  obtain ⟨d, hd, htd⟩ := (MvPolynomial.mem_vars_iff_mem_support t).1 ht
  have hcd := MvPolynomial.mem_support_iff.1 hd
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial] at hcd
  have hde : d ≠ Finsupp.single Δ 1 := by
    rintro rfl
    simp at hcd
  rw [if_neg (Ne.symm hde), sub_zero] at hcd
  have hne : Finsupp.toMultiset d ≠ {Δ} := fun h => hde ((toMultiset_eq_single_iff d Δ).1 h)
  exact len_lt_of_msupp hA (hp d (MvPolynomial.mem_support_iff.2 hcd)) hne t ((Finsupp.mem_toMultiset d t).2 htd)

end CompanionTheory.Groth.GrothendieckPhiBijection

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth.GrothendieckPhiBijection

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

theorem ell_phiOf (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hj : LSegJacquet k) (hJ : JCls k) (hAlt : AltSum k)
    (Lseg : Segment k → IrrGL k) (hL : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
    (hprod : ∀ (h N : ℕ) (Γ : Fin h → Segment k) (hd : ∑ a, (Lseg (Γ a)).1 = N),
      phiOf Lseg (∏ a, MvPolynomial.X (Γ a)) = toR (cl0 (prodIrr (fun a => Lseg (Γ a)) hd)))
    (Δ : Segment k) (p : MvPolynomial (Segment k) ℤ) :
    ell Δ (toR.symm (phiOf Lseg p)) = p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) := by
  classical
  have hm : ∀ s : Segment k →₀ ℕ, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial s 1))) =
      if s = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0 := by
    intro s
    obtain ⟨h, Γ, hΓ⟩ := exists_enum s
    rw [← prod_X_of_map s Γ hΓ, hprod h _ Γ rfl, AddEquiv.symm_apply_apply, ell_prod hA hj hJ hAlt Lseg hL, hΓ]
    by_cases hs : s = Finsupp.single Δ 1
    · rw [if_pos ((toMultiset_eq_single_iff s Δ).2 hs), if_pos hs]
    · rw [if_neg (fun h => hs ((toMultiset_eq_single_iff s Δ).1 h)), if_neg hs]
  have hm' : ∀ v, ell Δ (toR.symm (phiOf Lseg (MvPolynomial.monomial v (p.coeff v)))) =
      p.coeff v * (if v = Finsupp.single Δ 1 then (-1) ^ (Δ.len - 1) else 0) := by
    intro v
    have : MvPolynomial.monomial v (p.coeff v) = p.coeff v • MvPolynomial.monomial v (1 : ℤ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_zsmul, map_zsmul, map_zsmul, hm, smul_eq_mul]
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, hm']
  rw [Finset.sum_eq_single (Finsupp.single Δ 1)]
  · simp
  · intro b _ hb; simp [hb]
  · intro hn; rw [MvPolynomial.notMem_support_iff.1 hn]; simp

end CompanionTheory.Groth.GrothendieckPhiBijection

namespace CompanionTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [Fact (Assoc k)] [Fact (Comm k)] [Fact (One k)]

open GrothendieckPhiBijection in

theorem phiZ_bijective (hk : Steps k) (h1 : TriAut) (h2 : UniTri)
    (Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k)) (hZ : IsSegmentClass k Z) :
    Function.Bijective (phiOf (k := k) fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) := by
  have hA := CompanionTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  obtain ⟨Lseg, hL, hbij, hpre, hprod⟩ := phiL_main hk h2
  obtain ⟨hcls, -, -, -, -, -, -, -, hJ, hS, hAlt⟩ := hk
  have key : ∀ Δ : Segment k, ∃ p : MvPolynomial (Segment k) ℤ,
      phiOf Lseg p = toR (sg (⟨Δ.len * Δ.d, Z Δ⟩ : IrrGL k)) ∧
      ∃ (ε : ℤˣ) (q : MvPolynomial (Segment k) ℤ), (∀ t ∈ q.vars, t.len < Δ.len) ∧
        p = (ε : ℤ) • MvPolynomial.X Δ + q := by
    intro Δ
    obtain ⟨𝔫, h𝔫⟩ := hcls.exh ⟨Δ.len * Δ.d, Z Δ⟩
    obtain ⟨p, hp, hsupp⟩ := hpre 𝔫 _ h𝔫
    have hms := msupp_seg hA hcls.jac Z hZ hS Δ h𝔫
    have hce : p.coeff (Finsupp.single Δ 1) * (-1) ^ (Δ.len - 1) = 1 := by
      rw [← ell_phiOf hA hcls.jac hJ hAlt Lseg hL hprod Δ p, hp, AddEquiv.symm_apply_apply,
        ell_sg (hS Z hZ Δ).1 (hS Z hZ Δ).2]
    have hc : p.coeff (Finsupp.single Δ 1) = (-1) ^ (Δ.len - 1) := by
      have hsq : ((-1 : ℤ) ^ (Δ.len - 1)) * (-1) ^ (Δ.len - 1) = 1 := by
        rw [← mul_pow]; norm_num
      calc p.coeff (Finsupp.single Δ 1)
          = p.coeff (Finsupp.single Δ 1) * ((-1) ^ (Δ.len - 1) * (-1) ^ (Δ.len - 1)) := by rw [hsq, mul_one]
        _ = (-1) ^ (Δ.len - 1) := by rw [← mul_assoc, hce, one_mul]
    refine ⟨p, hp, (-1) ^ (Δ.len - 1),
      p - MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)),
      vars_lt hA p (fun s hs => (hsupp s hs).trans hms), ?_⟩
    have hX : (((-1 : ℤˣ) ^ (Δ.len - 1) : ℤˣ) : ℤ) • (MvPolynomial.X Δ : MvPolynomial (Segment k) ℤ) =
        MvPolynomial.monomial (Finsupp.single Δ 1) (p.coeff (Finsupp.single Δ 1)) := by
      rw [hc, MvPolynomial.X, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      push_cast
      rfl
    rw [hX]
    ring
  choose p hp ε q hq hpq using key
  have hψ : Function.Bijective (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) :=
    h1 (Segment k) Segment.len _ fun Δ => ⟨ε Δ, q Δ, hq Δ, by rw [MvPolynomial.eval₂Hom_X']; exact hpq Δ⟩
  have heq : phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) =
      (phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int ((phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩)).comp MvPolynomial.C)
        (((phiOf Lseg).comp (MvPolynomial.eval₂Hom (Int.castRingHom (MvPolynomial (Segment k) ℤ)) p)).comp
          MvPolynomial.C)) r
    · intro Δ
      rw [phiOf_X, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', hp Δ]
  rw [heq]
  exact hbij.comp hψ

end CompanionTheory.Groth

end
end

section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M Zc.Cos

set_option synthInstance.maxHeartbeats 400000

namespace CompanionTheory.Groth

theorem GrothendieckClassGeneralLinear.class_gl_eq_class {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (h : HasFiniteLength π) :
    clsGL π h = cl0 π := by
  unfold cl0; rw [dif_pos h]

theorem groth_of_steps (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      Cls k ∧ MulCls k ∧ Assoc k ∧ Comm k ∧ One k ∧ ProdList k ∧ Tri k ∧ MultOne k ∧ JCls k ∧ JSeg k ∧ AltSum k)
    (h1 : TriAut) (h2 : UniTri) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  intro k _ _ _ _ Z hZ
  have hk : Steps k := H k
  have : Fact (Assoc k) := ⟨hk.2.2.1⟩
  have : Fact (Comm k) := ⟨hk.2.2.2.1⟩
  have : Fact (One k) := ⟨hk.2.2.2.2.1⟩
  let e : MvPolynomial (Segment k) ℤ ≃+* R k := RingEquiv.ofBijective _ (phiZ_bijective hk h1 h2 Z hZ)
  have he : ∀ p, e p = phiOf (k := k) (fun Δ => ⟨Δ.len * Δ.d, Z Δ⟩) p := fun _ => rfl
  refine ⟨toR.trans e.symm.toAddEquiv, ?_, ?_, ?_⟩
  · show e.symm (toR (GrothGL.unit k)) = 1
    rw [toR_unit, map_one]
  · intro r t V W _ _ _ _ π₁ π₂ h₁ h₂ hs₁ hs₂ h
    show e.symm (toR (clsGL (prod₂ π₁ π₂) h)) = e.symm (toR (clsGL π₁ h₁)) * e.symm (toR (clsGL π₂ h₂))
    rw [GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, GrothendieckClassGeneralLinear.class_gl_eq_class, (hk.2.1 r t V W π₁ π₂ h₁ h₂ hs₁ hs₂).2, toR_mulR, map_mul]
  · intro Δ
    show e.symm (toR (Finsupp.single ⟨Δ.len * Δ.d, Z Δ⟩ 1)) = MvPolynomial.X Δ
    rw [RingEquiv.symm_apply_eq, he, phiOf_X]
    rfl

end CompanionTheory.Groth

end
end
