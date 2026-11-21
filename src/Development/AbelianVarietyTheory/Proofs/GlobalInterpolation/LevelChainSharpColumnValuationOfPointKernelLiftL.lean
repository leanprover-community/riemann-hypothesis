import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemFormsIffExistsEquivariantExtension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSumStatement
import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainTransitionIsExtKernelSum
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase

section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ}

namespace PtModel

variable (M : PtModel X i)

theorem inc_eq_image (v : X.A.vT) (p : M.Pt) :
    {p₁ | M.Inc v p p₁} =
      (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) '' {q | (p.2 v).Inc q} := by
  ext p₁
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p₁.2 v, h3, ?_⟩
    refine Prod.ext h1.symm ?_
    funext v'
    by_cases hv : v' = v
    · subst hv; simp
    · simp [Function.update_of_ne hv, h2 v' hv]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨rfl, fun v' hv => by simp [Function.update_of_ne hv], ?_⟩
    simpa using hq

theorem update_pt_injective (v : X.A.vT) (p : M.Pt) :
    Function.Injective (fun q => ((p.1, Function.update p.2 v q) : M.Pt)) := by
  intro q q' h
  have := congrArg (fun r : M.Pt => r.2 v) h
  simpa using this

theorem finsum_inc_eq (v : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, F p₁) =
      ∑ᶠ q ∈ {q | (p.2 v).Inc q}, F (p.1, Function.update p.2 v q) := by
  rw [inc_eq_image, finsum_mem_image (M.update_pt_injective v p).injOn]

theorem finite_inc_loc (v : X.A.vT) (p : M.Pt) : {q | (p.2 v).Inc q}.Finite := by
  have h := ((GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v).1 p).1
  rw [inc_eq_image] at h
  exact Set.Finite.of_finite_image h (M.update_pt_injective v p).injOn

theorem finsum_inc_comm (v v' : X.A.vT) (p : M.Pt) (F : M.Pt → M.Val) :
    (∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v' p₁ p₂}, F p₂) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v' p p₁}, ∑ᶠ p₂ ∈ {p₂ | M.Inc v p₁ p₂}, F p₂ := by
  by_cases hv : v = v'
  · subst hv; rfl
  have hv' : v' ≠ v := fun h => hv h.symm
  rw [finsum_inc_eq, finsum_inc_eq]
  simp only [finsum_inc_eq, Function.update_of_ne hv, Function.update_of_ne hv']
  rw [finsum_mem_comm _ (M.finite_inc_loc v p) (M.finite_inc_loc v' p)]
  simp only [Function.update_comm hv]

end PtModel

theorem formsStable_of_tgtEq : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → FormsStable X := by
  intro D u X Lv Kt hK
  refine ⟨fun i hi v φ hφ => ?_, fun i hi v v' φ hφ => ?_, fun i hi φ hφ => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) _).2 ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ⟩
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi) φ).1 hφ
    have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' φ Φ hΦ)
    have h2 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v' _ _ (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i (Lv i hi) v φ Φ hΦ)
    funext c
    rw [h1.1 c, h2.1 c]
    simp only []
    rw [(Lv i hi).finsum_inc_comm v v']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i (Lv i hi.le) φ).1 hφ
    exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X (i + 1) (Lv (i + 1) hi) _).2
      ⟨_, GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i (Lv i hi.le) (Lv (i + 1) hi) (Kt i hi) φ Φ (hK i hi) hΦ⟩

end GlobalTheory.LvT
end
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT

theorem count_incidence {G P C V : Type} [Group G] [MulAction G P] [Fintype C] [AddCommGroup V] [Module ℂ V]
    (rep : C → P) (hsurj : ∀ p, ∃ (c : C) (g : G), g • rep c = p)
    (hinj : ∀ (c c' : C) (g : G), g • rep c = rep c' → c = c')
    (hfin : ∀ c, Finite (MulAction.stabilizer G (rep c)))
    (I : P → P → Prop) (hup : ∀ p, {q | I p q}.Finite) (hdn : ∀ p, {q | I q p}.Finite)
    (hI : ∀ (g : G) p q, I p q → I (g • p) (g • q))
    (F : P → P → V) (hF : ∀ (g : G) p q, F (g • p) (g • q) = F p q) :
    ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ q ∈ {q | I (rep c) q}, F (rep c) q =
      ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ p ∈ {p | I p (rep c)}, F p (rep c) := by
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)
  have hfin' : ∀ p : P, Finite (MulAction.stabilizer G p) := by
    intro p
    obtain ⟨c, g, rfl⟩ := hsurj p
    haveI := hfin c
    exact Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (a := rep c) (g := g) rfl).toEquiv
  have hR : ∀ a : P, ∃! r, r ∈ Finset.univ.image rep ∧ r ∈ MulAction.orbit G a := by
    intro a
    obtain ⟨c, g, rfl⟩ := hsurj a
    refine ⟨rep c, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), g⁻¹, inv_smul_smul g _⟩, ?_⟩
    rintro r ⟨hr, γ, hγ⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hr
    have : c = c' := hinj c c' (γ * g) (by rw [mul_smul]; exact hγ)
    rw [this]
  have hrinj : Function.Injective rep := fun c c' h => hinj c c' 1 (by rw [one_smul, h])
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits G P P V (fun a => (hup a).toFinset) (fun b => (hdn b).toFinset) F
    (Finset.univ.image rep) (Finset.univ.image rep) (by intro a b; simp)
    (by intro γ a b h; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h ⊢; exact hI γ a b h)
    (fun γ a b _ => hF γ a b) hfin' hfin' hR hR
  rw [Finset.sum_image (fun a _ b _ h => hrinj h), Finset.sum_image (fun a _ b _ h => hrinj h)] at key
  have hq : ∀ (n : ℕ) (x : V), ((n : ℚ))⁻¹ • x = ((n : ℂ))⁻¹ • x := by
    intro n x
    change (algebraMap ℚ ℂ ((n : ℚ))⁻¹) • x = _
    simp
  simp only [hq] at key
  simp only [finsum_mem_eq_finite_toFinset_sum _ (hup _), finsum_mem_eq_finite_toFinset_sum _ (hdn _)]
  exact key

theorem levelChainUOperatorCommutation_of_pointPairLaw : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → (∀ i h, (Kt i h).UKLaw) → LevelChainUOperatorCommutation X := by
  intro D u X Lv Kt htgt huk i hi v φ hφ
  set M := Lv i hi.le with hM
  set M' := Lv (i + 1) hi with hM'
  let K : KerPt M M' := Kt i hi
  have hT : K.TgtEq := htgt i hi
  have hU : K.UKLaw := huk i hi
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  obtain ⟨hfinI, hstab, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X i M v
  obtain ⟨hfinI', -, -⟩ := GlobalTheory.T.levelPrime_incidence_finite_fibres_stable D u X (i + 1) M' v
  have h1 := GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X (i + 1) M' v _ _ (GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K φ Φ hT hΦ)
  have h2 := GlobalTheory.T.levelChainTransition_isExt_kernel_sum D u X i M M' K _ _ hT (GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ)
  have hpow : ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ ((D.R.t + 1) / 2) := by
    obtain ⟨k, hk⟩ := D.R.t_odd
    have e1 : (D.R.t + 1) / 2 = k + 1 := by omega
    have e2 : ((D.R.t : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [e1, e2, Real.rpow_natCast]
    push_cast; rfl
  have hwt : ∀ c, X.C.wt i c = ((Nat.card (MulAction.stabilizer M.G (M.rep c)) : ℂ))⁻¹ := by
    intro c
    rw [← M.card_stab]; rfl
  have hfs : ∀ c, Finite (MulAction.stabilizer M.G (M.rep c)) := by
    intro c
    apply Nat.finite_of_card_ne_zero
    rw [← M.card_stab]
    haveI := X.C.stabFin i c
    letI := X.C.stabGrp i c
    exact Nat.card_pos.ne'
  funext c'
  rw [hpow, Pi.smul_apply, h1.1 c', h2.1 c', ← Submodule.coe_smul]
  congr 1
  have key := count_incidence M.rep M.rep_surj M.rep_inj hfs (M.Inc v) (fun p => (hfinI p).1) (fun p => (hfinI p).2)
    (fun g p q h => (hstab g p q).1 h) (fun p q => K.k p (M'.rep c') (Φ q))
    (fun g p q => by rw [hΦ.2, K.src])
  have hL : ∀ c, K.k (M.rep c) (M'.rep c') (∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, Φ p₁) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, K.k (M.rep c) (M'.rep c') (Φ p₁) := by
    intro c
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, map_sum]
  simp only [hL, hwt]
  rw [key, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.smul_sum, smul_comm, ← hU v, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1]

end GlobalTheory.LvT
end
end

section
noncomputable section

namespace GlobalTheory.LvT.ValEq

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

section Local

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

theorem entry_mem (k : Matrix (Fin n) (Fin n) Lc.K) (hk : ∀ x ∈ Lc.std n, k.mulVec x ∈ Lc.std n) (a b : Fin n) :
    k a b ∈ Lc.O := by
  have h1 : (Pi.single b 1 : Fin n → Lc.K) ∈ Lc.std n := by
    rw [mem_std]; intro c
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  have := (mem_std _).1 (hk _ h1) a
  simpa using this

theorem f_sum (p : LocF.PP Lc n) (s : Finset (Fin n)) (c : Fin n → Lc.O) (e : Fin n → Fin n → Lc.K)
    (he : ∀ b, e b ∈ p.1.L) : p.1.f (∑ b ∈ s, c b • e b) = ∑ b ∈ s, Lc.res (c b) * p.1.f (e b) := by
  induction s using Finset.induction_on with
  | empty =>
    have := p.2.smul 0 0 p.1.L.zero_mem
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      p.2.add _ (p.1.L.smul_mem _ (he a)) _ (p.1.L.sum_mem fun b _ => p.1.L.smul_mem _ (he b)), ih,
      p.2.smul _ _ (he a)]

theorem exists_frame_ker (p : LocF.PP Lc n) :
    ∃ h : GL (Fin n) Lc.K, ∀ x, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) x ∈ p.ker ↔ x ∈ Lc.std n := by
  obtain ⟨h, hh⟩ := p.2.lat
  set e : Fin n → Fin n → Lc.K := fun b => Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single b 1) with he
  have heL : ∀ b, e b ∈ p.1.L := fun b => (hh _).2 (by
    rw [mem_std]; intro c
    by_cases h : c = b
    · subst h; simp
    · simp [h])
  have hf : ∀ y : Fin n → Lc.O, p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun b => (y b : Lc.K))) =
      ∑ b, Lc.res (y b) * p.1.f (e b) := by
    intro y
    rw [← f_sum p _ y e heL]
    congr 1
    ext a
    simp [he, Matrix.mulVec, dotProduct, Finset.sum_apply, Subring.smul_def, mul_comm]
  obtain ⟨a, ha⟩ : ∃ a, p.1.f (e a) ≠ 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨x, hx⟩ := p.2.ne
    have hxL : x ∈ p.1.L := by
      by_contra h'; exact hx (p.2.off x h')
    set y := Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x with hy
    have hxy : Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y = x := by
      rw [hy, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hyS := (mem_std _).1 ((hh y).1 (hxy ▸ hxL))
    have := hf fun b => ⟨y b, hyS b⟩
    apply hx
    rw [← hxy]
    simpa [hne] using this
  choose c0 hc0 using fun b => Lc.res_surj (p.1.f (e b) / p.1.f (e a))
  let c : Fin n → Lc.O := Function.update c0 a 1
  have hca : c a = 1 := by simp [c]
  have hc : ∀ b, Lc.res (c b) * p.1.f (e a) = p.1.f (e b) := by
    intro b
    by_cases hb : b = a
    · subst hb; simp [hca]
    · simp only [c, Function.update_of_ne hb, hc0]; field_simp
  let m : Matrix (Fin n) (Fin n) Lc.K := Matrix.updateRow 1 a fun b => ((q : Lc.K))⁻¹ * (c b : Lc.K)
  have hma : ∀ y, m.mulVec y a = ((q : Lc.K))⁻¹ * ∑ b, (c b : Lc.K) * y b := by
    intro y
    simp [m, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  have hmb : ∀ y b, b ≠ a → m.mulVec y b = y b := by
    intro y b hb
    simp [m, Matrix.mulVec, Matrix.updateRow_ne hb, dotProduct, Matrix.one_apply]
  have hsplit : ∀ y : Fin n → Lc.K, ∑ b, (c b : Lc.K) * y b = y a + ∑ b ∈ Finset.univ.erase a, (c b : Lc.K) * y b := by
    intro y
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), hca]; simp
  have hq := Lc.q_ne
  have hu : IsUnit m := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro y y' hyy
    have hb : ∀ b, b ≠ a → y b = y' b := fun b hb => by rw [← hmb y b hb, ← hmb y' b hb, hyy]
    have h1 := congrFun hyy a
    rw [hma, hma, hsplit, hsplit] at h1
    have h2 := mul_left_cancel₀ (inv_ne_zero hq) h1
    rw [Finset.sum_congr rfl fun b hb' => by rw [hb b (Finset.ne_of_mem_erase hb')]] at h2
    funext b
    by_cases hba : b = a
    · subst hba; exact add_right_cancel h2
    · exact hb b hba
  have key : ∀ y, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y ∈ p.ker ↔ m.mulVec y ∈ Lc.std n := by
    intro y
    have hres : ∀ hy : ∀ b, y b ∈ Lc.O, p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y) = 0 ↔
        ∃ t : Lc.O, ∑ b, (c b : Lc.K) * y b = (q : Lc.K) * t := by
      intro hy
      have h1 := hf fun b => ⟨y b, hy b⟩
      have h2 := Lc.res_ker (∑ b, c b * ⟨y b, hy b⟩)
      have h3 : ∑ b, Lc.res ⟨y b, hy b⟩ * p.1.f (e b) = Lc.res (∑ b, c b * ⟨y b, hy b⟩) * p.1.f (e a) := by
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hc b, map_mul]; ring
      have h4 : ((∑ b, c b * ⟨y b, hy b⟩ : Lc.O) : Lc.K) = ∑ b, (c b : Lc.K) * y b := by
        push_cast; rfl
      rw [h4] at h2
      rw [← h2]
      change p.1.f (Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) y) = _ at h1
      rw [h1, h3, mul_eq_zero, or_iff_left ha]
    constructor
    · rintro ⟨h1, h2⟩
      have hy := (mem_std _).1 ((hh y).1 h1)
      obtain ⟨t, ht⟩ := (hres hy).1 h2
      rw [mem_std]
      intro b
      by_cases hb : b = a
      · subst hb
        rw [hma, ht, inv_mul_cancel_left₀ hq]; exact t.2
      · rw [hmb _ _ hb]; exact hy b
    · intro h1
      rw [mem_std] at h1
      have ht : ∑ b, (c b : Lc.K) * y b = (q : Lc.K) * (⟨_, h1 a⟩ : Lc.O) := by
        simp only [hma]; rw [mul_inv_cancel_left₀ hq]
      have hy : ∀ b, y b ∈ Lc.O := by
        intro b
        by_cases hb : b = a
        · subst hb
          have : y b = (q : Lc.K) * m.mulVec y b - ∑ b' ∈ Finset.univ.erase b, (c b' : Lc.K) * y b' := by
            rw [eq_sub_iff_add_eq, ← hsplit, ht]
          rw [this]
          refine Lc.O.sub_mem (Lc.O.mul_mem (natCast_mem _ _) (h1 b)) (Lc.O.sum_mem fun b' hb' => Lc.O.mul_mem (c b').2 ?_)
          rw [← hmb y b' (Finset.ne_of_mem_erase hb')]; exact h1 b'
        · rw [← hmb y b hb]; exact h1 b
      exact ⟨(hh y).2 ((mem_std _).2 hy), (hres hy).2 ⟨_, ht⟩⟩
  obtain ⟨mu, hmu⟩ := hu
  refine ⟨h * mu⁻¹, fun x => ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, key, Matrix.mulVec_mulVec, ← hmu, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mulVec]

end Local

section Coeff

open Formalism.UG.P

theorem map_roundAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (l : DomWeight n) (g : GL (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial.map φ (roundAct R n l g f) =
      roundAct S n l (Matrix.GeneralLinearGroup.map φ g) (MvPolynomial.map φ f) := by
  unfold roundAct Formalism.UG.dwAct
  rw [wlocal_map_smul, wlocal_map_rowAct, ← map_inv]
  congr 1
  unfold detPow
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) =
      Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
    apply Units.ext
    simp [RingHom.map_det]
  rw [this, ← map_zpow (Units.map φ.toMonoidHom)]
  rfl

theorem invTr_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (g : GL (Fin n) R) :
    inside₂ S n (Matrix.GeneralLinearGroup.map φ g) = Matrix.GeneralLinearGroup.map φ (inside₂ R n g) := by
  apply Units.ext
  rfl

theorem roundAct_mem {R : Type} [CommRing R] {n : ℕ} (l : DomWeight n) (g : GL (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : f ∈ delSq R n l) : roundAct R n l g f ∈ delSq R n l := by
  rw [bridge_round_square_holds]
  exact (factSqStable R n l _).2 f hf

def roundL {n : ℕ} (l : DomWeight n) (g : GL (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  detPow ℂ n g (-l.detShift) • (Formalism.UG.dwAct ℂ n n g).toLinearMap

theorem blk_round_ten {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) (g : ι → GL (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blk (fun τ => roundAct ℂ n (l τ) (g τ)) (ten f) = ten fun τ => roundAct ℂ n (l τ) (g τ) (f τ) :=
  Formalism.MainNotions.product_first_zeroth_parts.blk_ten (fun τ => roundL (l τ) (g τ)) f

theorem blk_basis {ι : Type} [Fintype ι] {n : ℕ}
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n × Fin n) ℂ) (mon : ι × Fin n × Fin n →₀ ℕ) :
    blk F (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ mon) = ten fun τ => F τ (MvPolynomial.monomial
      (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1) :=
  Module.Basis.constr_basis _ _ _ _

theorem blk_round_mul {ι : Type} [Fintype ι] {n : ℕ} (l : ι → DomWeight n) (g k : ι → GL (Fin n) ℂ)
    (z : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blk (fun τ => roundAct ℂ n (l τ) (g τ * k τ)) z =
      blk (fun τ => roundAct ℂ n (l τ) (g τ)) (blk (fun τ => roundAct ℂ n (l τ) (k τ)) z) := by
  have : blk (fun τ => roundAct ℂ n (l τ) (g τ * k τ)) =
      blk (fun τ => roundAct ℂ n (l τ) (g τ)) ∘ₗ blk (fun τ => roundAct ℂ n (l τ) (k τ)) := by
    apply (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).ext
    intro mon
    rw [LinearMap.comp_apply, blk_basis, blk_basis, blk_round_ten]
    exact congrArg ten (funext fun τ => (factSqActMul ℂ n (l τ) _ _ _).2)
  rw [this]; rfl

variable {D : D7}

def embO (D : D7) (w : D.what₂.places.Pl) : Ow D w →+* ℂ := D.what₂.embLL.comp (Ow D w).subtype

theorem smul_mem_intSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (r : D.what₂.LL)
    (hr : r ∈ Ow D w) (z : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hz : z ∈ IntSpan D w lam) :
    D.what₂.embLL r • z ∈ IntSpan D w lam := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s, f, hs, hf, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨r * s, f, (Ow D w).mul_mem hr hs, hf, ?_⟩
    rw [smul_smul, map_mul]
  | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [smul_neg]; exact AddSubgroup.neg_mem _ hx

theorem ten_mem_intSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n)
    (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) (Ow D w)) (hf : ∀ τ, f τ ∈ delSq (Ow D w) n (lam τ)) :
    ten (fun τ => MvPolynomial.map (embO D w) (f τ)) ∈ IntSpan D w lam := by
  choose c hc using fun τ => Finsupp.mem_span_range_iff_exists_finsupp.1 (hf τ)
  have h1 : (fun τ => MvPolynomial.map (embO D w) (f τ)) = fun τ => ∑ a ∈ (c τ).support,
      embO D w (c τ a) • MvPolynomial.map (Int.castRingHom ℂ)
        (Formalism.GradedWeylDivisibility.applyWord ℤ a (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW)) := by
    funext τ
    rw [← hc τ, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wlocal_map_smul, wlocal_map_applyWord, wlocal_map_applyWord, wlocal_map_hw, wlocal_map_hw]
  rw [h1, ← Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, MultilinearMap.map_sum_finset]
  refine AddSubgroup.sum_mem _ fun a _ => ?_
  rw [MultilinearMap.map_smul_univ, Formalism.MainNotions.product_first_zeroth_parts.tenM_apply, ← map_prod]
  exact AddSubgroup.subset_closure ⟨_, fun τ => Formalism.GradedWeylDivisibility.applyWord ℤ (a τ) (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (lam τ).natW),
    (∏ τ, c τ (a τ)).2, fun τ => Submodule.subset_span ⟨a τ, rfl⟩, rfl⟩

theorem blk_mem_intSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (s : ℤ)
    (g : D.what₂.Tau → GL (Fin n) (Ow D w))
    (z : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) (hz : z ∈ IntSpan D w lam) :
    blk (fun τ => roundAct ℂ n (wSh (lam τ) s) (Matrix.GeneralLinearGroup.map (embO D w) (g τ))) z ∈
      IntSpan D w lam := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hx
    rw [map_smul, blk_round_ten]
    refine smul_mem_intSpan w lam r hr _ ?_
    have := ten_mem_intSpan w lam
      (fun τ => roundAct (Ow D w) n (wSh (lam τ) s) (g τ) (MvPolynomial.map (Int.castRingHom _) (f τ))) (fun τ => by
        rw [← Formalism.MainNotions.product_first_zeroth_parts.delSq_wSh _ (lam τ) s]
        apply roundAct_mem
        rw [Formalism.MainNotions.product_first_zeroth_parts.delSq_wSh]
        exact wlocal_map_weyl _ _ _ _ (hf τ))
    convert this using 2
    funext τ
    rw [map_roundAct, MvPolynomial.map_map, RingHom.ext_int ((embO D w).comp (Int.castRingHom _)) (Int.castRingHom ℂ)]
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem exists_lift {K L : Type} [Field K] [Field L] (A : Subring L) (j : K →+* L) {n : ℕ} (k : GL (Fin n) K)
    (h1 : ∀ a b, j ((k : Matrix (Fin n) (Fin n) K) a b) ∈ A)
    (h2 : ∀ a b, j (((k⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b) ∈ A) :
    ∃ g : GL (Fin n) A, ∀ a b, ((g : Matrix (Fin n) (Fin n) A) a b : L) = j ((k : Matrix (Fin n) (Fin n) K) a b) := by
  have key : ∀ (m m' : Matrix (Fin n) (Fin n) K) (hm : ∀ a b, j (m a b) ∈ A) (hm' : ∀ a b, j (m' a b) ∈ A),
      m * m' = 1 → (Matrix.of fun a b => (⟨_, hm a b⟩ : A)) * (Matrix.of fun a b => (⟨_, hm' a b⟩ : A)) = 1 := by
    intro m m' hm hm' h
    ext a b
    have := congrArg j (congrFun (congrFun h a) b)
    rw [Matrix.mul_apply, map_sum] at this
    rw [Matrix.mul_apply]
    by_cases hab : a = b <;> simpa [Matrix.one_apply, hab] using this
  exact ⟨⟨_, _, key _ _ h1 h2 (Units.mul_inv k), key _ _ h2 h1 (Units.inv_mul k)⟩, fun _ _ => rfl⟩

theorem mem_Ow_of_pow (w : D.what₂.places.Pl) (ζ : D.what₂.LL) (k : ℕ) (hk : 0 < k) (h : ζ ^ k = 1) : ζ ∈ Ow D w := by
  change (0 : WithTop ℤ) ≤ D.what₂.places.val w ζ
  have h1 := congrArg (D.what₂.places.val w) h
  rw [AddValuation.map_pow, AddValuation.map_one] at h1
  induction hv : D.what₂.places.val w ζ using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    rw [hv, ← WithTop.coe_nsmul, ← WithTop.coe_zero, WithTop.coe_inj, nsmul_eq_mul, mul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (by exact_mod_cast hk.ne')
    · rw [h1]; exact le_rfl

end Coeff

section Main

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ} {M : PtModel X i} (Co : M.Coord)

theorem mov_mul (w : D.what₂.places.Pl) (h k : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K)
    (z : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) :
    Co.mov w (fun v => h v * k v) z = Co.mov w h (Co.mov w k z) := by
  unfold PtModel.Coord.mov
  rw [← blk_round_mul]
  have : ∀ τ, Co.mv w (fun v => h v * k v) τ = Co.mv w h τ * Co.mv w k τ := by
    intro τ
    unfold PtModel.Coord.mv
    dsimp only
    split_ifs
    · rw [map_mul]
    · rw [map_mul, invTr_mul]
  simp only [this]

theorem mov_mem (w : D.what₂.places.Pl) (hw : OverT X w) (k : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K)
    (hk : ∀ v x, Matrix.mulVec (k v : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (M.Lc v).K) x ∈ (M.Lc v).std (D.R.N i) ↔
      x ∈ (M.Lc v).std (D.R.N i))
    (z : MvPolynomial (D.what₂.Tau × Fin (D.R.N i) × Fin (D.R.N i)) ℂ) (hz : z ∈ IntSpan D w (X.fm.lam i)) :
    Co.mov w k z ∈ IntSpan D w (X.fm.lam i) := by
  have hl : ∀ v, ∃ g : GL (Fin (D.R.N i)) (Ow D w), Matrix.GeneralLinearGroup.map (embO D w) g =
      Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v)) (k v) := by
    intro v
    obtain ⟨g, hg⟩ := exists_lift (Ow D w) (Co.j w v) (k v)
      (fun a b => (Co.j_int w hw v _).2 (entry_mem _ (fun x hx => (hk v x).2 hx) a b))
      (fun a b => (Co.j_int w hw v _).2 (entry_mem _ (fun x hx => (hk v _).1 (by
        rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec])) a b))
    refine ⟨g, Units.ext (Matrix.ext fun a b => ?_)⟩
    exact congrArg D.what₂.embLL (hg a b)
  choose g hg using hl
  have := blk_mem_intSpan w (X.fm.lam i) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)
    (fun τ => if X.fm.seenP w then g ((X.fm.tauOf w).symm τ) else inside₂ _ _ (g ((X.fm.tauOf w).symm τ))) z hz
  have e : ∀ τ, Co.mv w k τ = Matrix.GeneralLinearGroup.map (embO D w)
      (if X.fm.seenP w then g ((X.fm.tauOf w).symm τ) else inside₂ _ _ (g ((X.fm.tauOf w).symm τ))) := by
    intro τ
    unfold PtModel.Coord.mv
    dsimp only
    split_ifs
    · rw [hg]
    · rw [← invTr_map, hg]
  unfold PtModel.Coord.mov PtModel.lamT
  simp only [e]
  exact this

theorem valB_laws : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → ∀ (V : Finset X.A.vT) (p : M.Pt), (0 : M.Val) ∈ Co.valB w V p ∧ (∀ y ∈ Co.valB w V p, ∀ y' ∈ Co.valB w V p, y + y' ∈ Co.valB w V p) ∧ (∀ r ∈ Ow D w, ∀ y ∈ Co.valB w V p, D.what₂.embLL r • y ∈ Co.valB w V p) ∧ ∀ (g : M.G), ∀ y ∈ Co.valB w V p, M.act g y ∈ Co.valB w V (g • p) := by
  intro D u X i M Co hCo w hw V p
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : ∀ v, ∃ h, M.IsFrameS v h
        (if X.fm.seenP w = true ∧ v ∉ V then ((p.2 v).1.L : Set _) else (p.2 v).ker) := by
      intro v
      split_ifs
      · exact (p.2 v).2.lat
      · exact exists_frame_ker (p.2 v)
    choose h hh using this
    exact ⟨h, hh, 0, AddSubgroup.zero_mem _, by rw [map_zero, map_zero]⟩
  · rintro y ⟨h, hh, z, hz, hy⟩ y' ⟨h', hh', z', hz', hy'⟩
    refine ⟨h, hh, z + Co.mov w (fun v => (h v)⁻¹ * h' v) z',
      AddSubgroup.add_mem _ hz (mov_mem Co w hw _ (fun v x => ?_) z' hz'), ?_⟩
    · rw [← hh v, ← hh' v x, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
    · rw [map_add, map_add, ← mov_mul, hy, hy']
      simp only [mul_inv_cancel_left]
  · rintro r hr y ⟨h, hh, z, hz, hy⟩
    exact ⟨h, hh, _, smul_mem_intSpan w _ r hr z hz, by rw [map_smul, map_smul, hy]⟩
  · rintro g y ⟨h, hh, z, hz, hy⟩
    obtain ⟨ζ, k, hk, hζ, hact⟩ := hCo.act_co w hw g
    refine ⟨fun v => M.loc v g * h v, fun v x => ?_, _,
      smul_mem_intSpan w _ ζ (mem_Ow_of_pow w ζ k hk hζ) z hz, ?_⟩
    · rw [← hh v x, Units.val_mul, ← Matrix.mulVec_mulVec]
      have ha := M.smul_snd g p v (Matrix.mulVec (h v : Matrix _ _ (M.Lc v).K) x)
      split_ifs
      · exact ha.1
      · unfold LocF.PP.ker
        simp only [Set.mem_ofPred_eq]
        rw [ha.1, ha.2]
    · rw [hact, hy, map_smul, mov_mul]

end Main

end GlobalTheory.LvT.ValEq
end
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → ∀ (V : Finset X.A.vT) (p : M.Pt), (0 : M.Val) ∈ Co.valB w V p ∧ (∀ y ∈ Co.valB w V p, ∀ y' ∈ Co.valB w V p, y + y' ∈ Co.valB w V p) ∧ (∀ r ∈ Ow D w, ∀ y ∈ Co.valB w V p, D.what₂.embLL r • y ∈ Co.valB w V p) ∧ ∀ (g : M.G), ∀ y ∈ Co.valB w V p, M.act g y ∈ Co.valB w V (g • p) := by
  first | exact @GlobalTheory.LvT.ValEq.valB_laws | exact GlobalTheory.LvT.ValEq.valB_laws | (intros; apply GlobalTheory.LvT.ValEq.valB_laws <;> assumption)
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

theorem valB_of_inc : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord) (w : D.what₂.places.Pl) (V : Finset X.A.vT) (v : X.A.vT) (p p₁ : M.Pt), X.fm.seenP w = true → v ∈ V → M.Inc v p p₁ → Co.valB w V p₁ = Co.valB w (V.erase v) p := by
  intro D u X i M Co w V v p p₁ hw hv hI
  obtain ⟨-, hoff, x, -, -, hk, -⟩ := hI
  have key : ∀ v', (if X.fm.seenP w = true ∧ v' ∉ V then ((p₁.2 v').1.L : Set _) else (p₁.2 v').ker) =
      (if X.fm.seenP w = true ∧ v' ∉ V.erase v then ((p.2 v').1.L : Set _) else (p.2 v').ker) := by
    intro v'
    by_cases h : v' = v
    · subst h
      rw [if_neg (fun h => h.2 hv), if_pos ⟨hw, Finset.notMem_erase _ _⟩, hk]
    · rw [hoff v' h]
      have : v' ∈ V.erase v ↔ v' ∈ V := by simp [h]
      simp only [this]
  unfold PtModel.Coord.valB
  simp only [key]

end GlobalTheory.LvT
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  first | exact @GlobalTheory.LvT.pow_smul_mem_valB_erase | exact GlobalTheory.LvT.pow_smul_mem_valB_erase | (intros; apply GlobalTheory.LvT.pow_smul_mem_valB_erase <;> assumption)
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT.UKS

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

theorem emb_mem_Fi (X : Ch D u) (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem inv_natCast_mem (w : D.what₂.places.Pl) (n : ℕ) (hn : ¬ D.what₂.places.resChar w ∣ n) :
    ((n : D.what₂.LL))⁻¹ ∈ Ow D w := by
  set p := D.what₂.places.resChar w with hp
  have hpr : p.Prime := D.what₂.places.resChar_prime w
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hpr).2 hn
  have hint : ∀ z : ℤ, 0 ≤ D.what₂.places.val w (z : D.what₂.LL) := fun z => intCast_mem (Ow D w) z
  have hbez : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n) = 1 := by
    have := Nat.gcd_eq_gcd_ab p n
    rw [hcop.gcd_eq_one] at this
    exact_mod_cast this.symm
  have hbez' : (p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL) + (n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : D.what₂.LL)) hbez
  have hvp : 0 < D.what₂.places.val w (p : D.what₂.LL) := by
    rw [hp, D.what₂.places.val_resChar w]
    have := D.what₂.places.ramIdx_pos w
    exact_mod_cast this
  have hvn : D.what₂.places.val w (n : D.what₂.LL) = 0 := by
    have h0 : 0 ≤ D.what₂.places.val w (n : D.what₂.LL) := by exact_mod_cast hint n
    by_contra hne
    have hpos : 0 < D.what₂.places.val w (n : D.what₂.LL) := lt_of_le_of_ne h0 (Ne.symm hne)
    have h1 : 0 < D.what₂.places.val w ((p : D.what₂.LL) * ((Nat.gcdA p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hvp (hint _)
    have h2 : 0 < D.what₂.places.val w ((n : D.what₂.LL) * ((Nat.gcdB p n : ℤ) : D.what₂.LL)) := by
      rw [AddValuation.map_mul]; exact add_pos_of_pos_of_nonneg hpos (hint _)
    have h3 := (D.what₂.places.val w).map_lt_add h1 h2
    rw [hbez', AddValuation.map_one] at h3
    exact lt_irrefl _ h3
  show 0 ≤ D.what₂.places.val w ((n : D.what₂.LL))⁻¹
  rw [AddValuation.map_inv, hvn]
  simp

section
variable {i : ℕ} {M : PtModel X i} (Co : M.Coord)

def ExtIn (w : D.what₂.places.Pl) (V : Finset X.A.vT) (φ : Fn X i) : Prop :=
  ∃ Φ, M.IsExt φ Φ ∧ ∀ p, Φ p ∈ Co.valB w V p

variable {Co}

theorem extIn_of_valIn (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i)
    (h : M.ValIn (Co.valB w V) φ) : ExtIn Co w V φ := by
  obtain ⟨Φ, hΦ⟩ := (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).1 hφ
  refine ⟨Φ, hΦ, fun p => ?_⟩
  obtain ⟨c, g, rfl⟩ := M.rep_surj p
  obtain ⟨y, hy, hyc⟩ := h c
  have : Φ (M.rep c) = y := Subtype.ext ((hΦ.1 c).symm.trans hyc)
  rw [hΦ.2, this]
  exact (GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw V _).2.2.2 g y hy

theorem ExtIn.mem_Fi {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : φ ∈ X.fm.Fi i := by
  obtain ⟨Φ, hΦ, -⟩ := h
  exact (GlobalTheory.T.mem_forms_iff_exists_equivariant_extension D u X i M φ).2 ⟨Φ, hΦ⟩

theorem ExtIn.valIn {w V} {φ : Fn X i} (h : ExtIn Co w V φ) : M.ValIn (Co.valB w V) φ := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact fun c => ⟨_, h _, hΦ.1 c⟩

theorem isExt_smul {φ : Fn X i} {Φ} (h : M.IsExt φ Φ) (a : ℂ) : M.IsExt (a • φ) (fun p => a • Φ p) := by
  refine ⟨fun c => ?_, fun g p => ?_⟩
  · show a • φ c = _
    rw [h.1 c]; rfl
  · simp only [h.2, map_smul]

theorem pow_smul_mem (hC : Co.Ok) {w} (hw : OverT X w) {V p y} (hy : y ∈ Co.valB w V p) (n : ℕ) :
    ((X.A.T : ℂ) ^ n) • y ∈ Co.valB w V p := by
  have := (GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw V p).2.2.1 ((X.A.T : D.what₂.LL) ^ n)
    (pow_mem (natCast_mem _ _) n) y hy
  simpa using this

theorem ExtIn.pow_smul (hC : Co.Ok) {w} (hw : OverT X w) {V} {φ : Fn X i} (h : ExtIn Co w V φ) (n : ℕ) :
    ExtIn Co w V (((X.A.T : ℂ) ^ n) • φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  exact ⟨_, isExt_smul hΦ _, fun p => pow_smul_mem hC hw (h p) n⟩

theorem ExtIn.uop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V v} (hv : v ∈ V)
    {φ : Fn X i} (h : ExtIn Co w V φ) : ExtIn Co w (V.erase v) (Uop X i v φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, GlobalTheory.T.isExt_Uop_finsum_inc_of_isExt D u X i M v φ Φ hΦ, fun p => ?_⟩
  have hv' := GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X i M Co hC w hw (V.erase v) p
  refine finsum_mem_induction (fun y => y ∈ Co.valB w (V.erase v) p) hv'.1
    (fun y y' hy hy' => hv'.2.1 y hy y' hy') fun p₁ hp₁ => ?_
  rw [← GlobalTheory.LvT.valB_of_inc D u X i M Co w V v p p₁ hs hv hp₁]
  exact h p₁

theorem ExtIn.uops (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (l : List X.A.vT) (hl : l.Nodup) (hV : ∀ v ∈ l, v ∈ V) :
    ExtIn Co w (V \ l.toFinset) (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id φ) := by
  induction l with
  | nil => simpa using h
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    have h1 := ih hl.2 (fun v' hv' => hV v' (List.mem_cons_of_mem _ hv'))
    have h2 := h1.uop hC hw hs (v := v) (by simp [hl.1, hV v List.mem_cons_self])
    have e : (V \ l.toFinset).erase v = V \ (v :: l).toFinset := by
      ext x; simp; tauto
    rw [e] at h2
    exact h2

theorem ExtIn.drop (hC : Co.Ok) {w} (hw : OverT X w) (hs : X.fm.seenP w = true) {V}
    {φ : Fn X i} (h : ExtIn Co w V φ) (A : Finset X.A.vT) (hA : A ⊆ V) :
    ExtIn Co w (V \ A)
      (((X.A.T : ℂ) ^ (∑ v ∈ A, (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩)) • φ) := by
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  induction A using Finset.induction_on with
  | empty => simpa using h
  | insert v A hv ih =>
    obtain ⟨Φ, hΦ, h1⟩ := ih ((Finset.subset_insert _ _).trans hA)
    have e : (V \ A).erase v = V \ insert v A := by
      ext x; simp; tauto
    rw [Finset.sum_insert hv, zpow_add₀ hT, mul_smul, ← e]
    exact ⟨_, isExt_smul hΦ _, fun p => GlobalTheory.T.levelPrime_pow_smul_mem_valueLattice_erase D u X i M Co hC w hw hs _ v
      (by simp [hv, hA (Finset.mem_insert_self _ _)]) p _ (h1 p)⟩

end

theorem extIn_K {i : ℕ} {M : PtModel X i} {M' : PtModel X (i + 1)} {Co : M.Coord} {Co' : M'.Coord}
    (hC' : Co'.Ok) (K : KerPt M M') (hK : K.TgtEq) {w} (hw : OverT X w)
    (hst : ∀ c, ¬ X.A.T ∣ Nat.card (X.C.stab i c)) (a : ℂ) {V}
    (ha : ∀ p p', ∀ y ∈ Co.valB w ∅ p, a • K.k p p' y ∈ Co'.valB w V p')
    {φ : Fn X i} (h : ExtIn Co w ∅ φ) : ExtIn Co' w V (a • KT X i φ) := by
  obtain ⟨Φ, hΦ, h⟩ := h
  refine ⟨_, isExt_smul (GlobalTheory.LvT.isExt_KT D u X i M M' K φ Φ hK hΦ) a, fun p' => ?_⟩
  have hv := GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws D u X (i + 1) M' Co' hC' w hw V p'
  simp only [Finset.smul_sum]
  refine Finset.sum_induction _ (fun y => y ∈ Co'.valB w V p') (fun y y' hy hy' => hv.2.1 y hy y' hy') hv.1
    fun c _ => ?_
  rw [smul_comm]
  have := hv.2.2.1 _ (inv_natCast_mem w (Nat.card (X.C.stab i c)) (by rw [show _ = _ from hw]; exact hst c)) _
    (ha _ p' _ (h (M.rep c)))
  simpa [ColumnChain.wt] using this

theorem ukSharp (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Vt : ValTie Lv) (Kt : KerTie Lv)
    (hK : KerLaws Vt Kt) (hst : StabUnit X) (hW : WtBounds X) : UKSharp X := by
  intro w hw i hi x hx
  have hT : (X.A.T : ℂ) ≠ 0 := by exact_mod_cast X.A.T_prime.ne_zero
  have hC := (Vt i hi.le).2
  have hC' := (Vt (i + 1) hi).2
  have h0 : ExtIn (Vt i hi.le).1 w ∅ (X.fm.emb i x) :=
    extIn_of_valIn hC hw (emb_mem_Fi X i x) ((hC.S_on w hw _ (emb_mem_Fi X i x)).1 ⟨x, hx, rfl⟩)
  suffices h : ExtIn (Vt (i + 1) hi).1 w ∅
      (tpow X (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) •
        Uprod X (i + 1) w (KT X i (X.fm.emb i x))) from (hC'.S_on w hw _ h.mem_Fi).2 h.valIn
  by_cases hs : X.fm.seenP w = true
  · have h1 := extIn_K hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) _ (hK.intP i hi w hw hs) h0
    have h2 := h1.uops hC' hw hs (VVT X w).toList (Finset.nodup_toList _) (fun v _ => Finset.mem_univ v)
    have h3 := h2.drop hC' hw hs _ (Finset.Subset.refl _)
    rw [Finset.sdiff_self, Finset.toList_toFinset, map_smul, smul_smul, ← zpow_add₀ hT] at h3
    set e : ℤ := ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ +
      (((D.R.f * D.R.N i : ℕ) : ℤ) + ∑ τ, X.C.sDiv i τ) with he
    have hle : e ≤ ((2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by
      have a1 : ∑ v ∈ Finset.univ \ VVT X w, (PtModel.lamT X (i + 1) (X.fm.tauOf w v)).w ⟨0, D.R.N_pos _⟩ ≤
          ∑ τ, (Wt X τ : ℤ) := by
        rw [← Equiv.sum_comp (X.fm.tauOf w)]
        refine le_trans (Finset.sum_le_sum fun v hv => (hW.2 i hi _).2.2.2 ?_)
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Int.natCast_nonneg _)
        simpa [VVT, hs] using hv
      have a2 : ∑ τ, X.C.sDiv i τ ≤ ∑ τ, (Wt X τ : ℤ) := Finset.sum_le_sum fun τ _ => (hW.2 i hi τ).2.1
      have a3 : D.R.f * D.R.N i ≤ D.R.f * D.R.N D.R.m :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _)
      have a3' : ((D.R.f * D.R.N i : ℕ) : ℤ) ≤ ((D.R.f * D.R.N D.R.m : ℕ) : ℤ) := by exact_mod_cast a3
      rw [he, Nat.cast_add, Nat.cast_mul 2, Nat.cast_sum]
      simp only [Nat.cast_ofNat]
      linarith
    obtain ⟨n, hn⟩ := Int.le.dest hle
    have h4 := h3.pow_smul hC' hw n
    rw [smul_smul, ← zpow_natCast, ← zpow_add₀ hT, add_comm (n : ℤ), hn, zpow_natCast] at h4
    rw [if_pos hs]
    exact h4
  · have hs' : X.fm.seenP w = false := by simpa using hs
    have h1 := extIn_K (V := ∅) hC' (Kt i hi) (hK.tgt i hi) hw (hst i hi.le) 1 (fun p p' y hy => by
      obtain ⟨y', hy', e⟩ := hK.bar i hi w hw hs' p p' y hy
      rw [one_smul, e]
      exact pow_smul_mem hC' hw hy' _) h0
    rw [if_neg hs]
    simpa [tpow, Uprod, VVT, hs'] using h1

end GlobalTheory.LvT.UKS
end
end

section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace ColSharp

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

noncomputable def colUp (i : ℕ) : Fn X 0 →ₗ[ℂ] Fn X i :=
  Nat.rec (motive := fun i => Fn X 0 →ₗ[ℂ] Fn X i) LinearMap.id (fun i g => KT X i ∘ₗ g) i

theorem colUp_eq (i : ℕ) (φ : Fn X 0) : colUp X i φ = Formalism.ThetaLiftIndependence.chainOpM X.C.wt X.C.Kmap i φ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    show KT X i (colUp X i φ) = _
    rw [ih]; rfl

theorem colT_eq (φ : Fn X 0) : colT X φ = colUp X D.R.m φ := (colUp_eq X _ φ).symm

theorem emb_mem (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

variable {X}

theorem fold_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (l : List X.A.vT) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ ∈ X.fm.Fi i := by
  induction l with
  | nil => exact hφ
  | cons v l ih => exact hF.1 i hi v _ ih

theorem Uprod_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i}
    (hφ : φ ∈ X.fm.Fi i) : Uprod X i w φ ∈ X.fm.Fi i := fold_mem hF hi _ hφ

theorem Upow_mem (hF : FormsStable X) (w : D.what₂.places.Pl) (n : ℕ) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : (Uprod X 0 w ^ n) φ ∈ X.fm.Fi 0 := by
  induction n with
  | zero => exact hφ
  | succ n ih => rw [pow_succ']; exact Uprod_mem hF (Nat.zero_le _) w ih

theorem colUp_mem (hF : FormsStable X) {i : ℕ} (hi : i ≤ D.R.m) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : colUp X i φ ∈ X.fm.Fi i := by
  induction i with
  | zero => exact hφ
  | succ i ih => exact hF.2.2 i hi _ (ih (Nat.le_of_succ_le hi))

theorem scalar_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) :
    ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ s := by
  have h : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) := by
    have : ((D.R.t + 1 : ℕ) : ℝ) = ((2 * s : ℕ) : ℝ) := by rw [hs]
    push_cast at this; linarith
  rw [h, Real.rpow_natCast]; push_cast; rfl

theorem fold_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (l : List X.A.vT) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    (l.foldr (fun v g => (Uop X (i + 1) v).comp g) LinearMap.id : Fn X (i + 1) →ₗ[ℂ] Fn X (i + 1)) (KT X i φ) =
      (X.A.T : ℂ) ^ (s * l.length) •
        KT X i ((l.foldr (fun v g => (Uop X i v).comp g) LinearMap.id : Fn X i →ₗ[ℂ] Fn X i) φ) := by
  induction l with
  | nil => simp
  | cons v l ih =>
    rw [List.foldr_cons, List.foldr_cons, LinearMap.comp_apply, LinearMap.comp_apply, ih, map_smul,
      h4 i hi v _ (fold_mem hF hi.le l hφ), scalar_eq hs, smul_smul, ← pow_add, List.length_cons, Nat.mul_succ]

theorem Uprod_comm (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i < D.R.m) (w : D.what₂.places.Pl) {φ : Fn X i} (hφ : φ ∈ X.fm.Fi i) :
    Uprod X (i + 1) w (KT X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card) • KT X i (Uprod X i w φ) := by
  rw [← Finset.length_toList]; exact fold_comm hF h4 hs hi _ hφ

theorem Uprod_colUp (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s) {i : ℕ}
    (hi : i ≤ D.R.m) (w : D.what₂.places.Pl) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    Uprod X i w (colUp X i φ) = (X.A.T : ℂ) ^ (s * (VVT X w).card * i) • colUp X i (Uprod X 0 w φ) := by
  induction i with
  | zero => simp [colUp]
  | succ i ih =>
    have hi' : i < D.R.m := hi
    show Uprod X (i + 1) w (KT X i (colUp X i φ)) = _ • KT X i (colUp X i (Uprod X 0 w φ))
    rw [Uprod_comm hF h4 hs hi' w (colUp_mem hF hi'.le hφ), ih hi'.le, map_smul, smul_smul, ← pow_add,
      Nat.mul_succ, Nat.add_comm (s * _)]

theorem chain_into (hF : FormsStable X) (h4 : LevelChainUOperatorCommutation X) {s : ℕ} (hs : D.R.t + 1 = 2 * s)
    (w : D.what₂.places.Pl) (e : ℕ)
    (hU : ∀ i, i < D.R.m → Into X w (fun φ => tpow X e • Uprod X (i + 1) w (KT X i φ))
      (X.fm.S i w) (X.fm.S (i + 1) w)) {i : ℕ} (hi : i ≤ D.R.m) :
    Into X w (fun φ => (X.A.T : ℂ) ^ (i * e + s * (VVT X w).card * ∑ j ∈ Finset.range (i + 1), j) •
      colUp X i ((Uprod X 0 w ^ i) φ)) (X.fm.S 0 w) (X.fm.S i w) := by
  induction i with
  | zero => intro x hx; exact ⟨x, hx, by simp [colUp]⟩
  | succ i ih =>
    have hi' : i < D.R.m := hi
    intro x hx
    obtain ⟨y, hy, hy'⟩ := ih hi'.le x hx
    obtain ⟨z, hz, hz'⟩ := hU i hi' y hy
    refine ⟨z, hz, ?_⟩
    have hm := Upow_mem hF w i (emb_mem X 0 x)
    have key := Uprod_colUp hF h4 hs hi w hm
    have e1 : colUp X (i + 1) ((Uprod X 0 w ^ i) (X.fm.emb 0 x)) =
      KT X i (colUp X i ((Uprod X 0 w ^ i) (X.fm.emb 0 x))) := rfl
    rw [hz']
    beta_reduce at hy' ⊢
    rw [hy', map_smul, map_smul, ← e1, key, pow_succ' (Uprod X 0 w) i, Module.End.mul_apply, tpow,
      smul_smul, smul_smul, ← pow_add, ← pow_add, Finset.sum_range_succ _ (i + 1)]
    congr 2
    ring

theorem card_VVT {w : D.what₂.places.Pl} (h : X.fm.seenP w = true) : (VVT X w).card = (tops D).card := by
  unfold VVT
  rw [if_pos h]
  refine Finset.card_bij (fun v _ => X.fm.tauOf w v) (fun v hv => (Finset.mem_filter.1 hv).2)
    (fun a _ b _ hab => (X.fm.tauOf w).injective hab) (fun τ hτ => ?_)
  exact ⟨(X.fm.tauOf w).symm τ, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using hτ⟩, by simp⟩

theorem expT_nonneg (hW : WtBounds X) (w : D.what₂.places.Pl) : 0 ≤ expT X w := by
  refine mul_nonneg (Int.natCast_nonneg _) (Finset.sum_nonneg fun v hv => hW.1 _ ?_)
  unfold VVT at hv
  split_ifs at hv
  · exact (Finset.mem_filter.1 hv).2
  · simp at hv

theorem val_pow {w : D.what₂.places.Pl} (hw : OverT X w) (k : ℕ) :
    D.what₂.places.val w ((X.A.T : D.what₂.LL) ^ k) = (((D.what₂.places.ramIdx w * k : ℕ) : ℤ) : WithTop ℤ) := by
  have h := D.what₂.places.val_resChar w
  rw [show D.what₂.places.resChar w = X.A.T from hw] at h
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AddValuation.map_mul, ih, h, ← WithTop.coe_add]
    congr 1

theorem quot_mem {w : D.what₂.places.Pl} (hw : OverT X w) {c : D.what₂.LL} {n : ℤ}
    (hc : D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ)) (a b : ℕ)
    (h : ((D.what₂.places.ramIdx w * b : ℕ) : ℤ) ≤ n) :
    c * (X.A.T : D.what₂.LL) ^ a * ((X.A.T : D.what₂.LL) ^ b)⁻¹ ∈ Ow D w := by
  show (0 : WithTop ℤ) ≤ D.what₂.places.val w _
  rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_inv, hc, val_pow hw, val_pow hw]
  rw [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add, ← WithTop.coe_add]
  have : (0 : ℤ) ≤ ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) := Int.natCast_nonneg _
  exact_mod_cast (by omega : (0 : ℤ) ≤ n + ((D.what₂.places.ramIdx w * a : ℕ) : ℤ) + -((D.what₂.places.ramIdx w * b : ℕ) : ℤ))

theorem loss_eq {s : ℕ} (hs : D.R.t + 1 = 2 * s) (w : D.what₂.places.Pl) :
    ((D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      s * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) = (D.R.m : ℝ) * ET X w := by
  unfold ET
  by_cases h : X.fm.seenP w = true
  · rw [if_pos h, if_pos h, card_VVT h]
    unfold ETpi
    have h1 : ((D.R.t : ℝ) + 1) = 2 * s := by exact_mod_cast hs
    have h2 : ((∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) : ℝ) * 2 = ((D.R.m : ℝ) + 1) * D.R.m := by
      have := Finset.sum_range_id_mul_two (D.R.m + 1)
      rw [Nat.add_sub_cancel] at this
      exact_mod_cast this
    rw [h1]
    generalize (∑ j ∈ Finset.range (D.R.m + 1), j : ℕ) = S at h2 ⊢
    push_cast
    linear_combination ((s : ℝ) * ((tops D).card : ℝ) / 2) * h2
  · have : VVT X w = ∅ := by unfold VVT; rw [if_neg h]
    rw [if_neg h, if_neg h, this]
    simp

end ColSharp

open ColSharp in

theorem levelChainSharpColumnValuation_of_stability : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u),
    FormsStable X → LevelChainUOperatorCommutation X → UKSharp X → WtBounds X → Conclusion5Sharp X := by
  intro D u X hF h4 hU hW w hw c n hc hn x' hx'
  obtain ⟨x, hx, hxx⟩ := hx'
  obtain ⟨s0, hs0⟩ := D.R.t_odd
  have hs : D.R.t + 1 = 2 * (s0 + 1) := by omega
  obtain ⟨y, hy, hy'⟩ := chain_into hF h4 hs w _ (hU w hw) (le_refl D.R.m) x hx.1
  rw [← loss_eq (X := X) hs w] at hn
  set b := D.R.m * (if X.fm.seenP w then 2 * ∑ τ, Wt X τ + D.R.f * D.R.N D.R.m else 0) +
      (s0 + 1) * (VVT X w).card * ∑ j ∈ Finset.range (D.R.m + 1), j with hb
  obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (expT_nonneg hW w)
  have hmem := quot_mem hw hc a b (by exact_mod_cast hn)
  refine ⟨(⟨_, hmem⟩ : Ow D w) • y, (X.fm.S D.R.m w).smul_mem _ hy, ?_⟩
  have hT : (X.A.T : ℂ) ^ b ≠ 0 := pow_ne_zero _ (by exact_mod_cast X.A.T_prime.ne_zero)
  beta_reduce at hy' ⊢
  rw [Subring.smul_def, LinearMap.map_smulₛₗ, hy', hxx, colT_eq, ha, LinearMap.smul_apply, map_smul,
    smul_smul, smul_smul, zpow_natCast]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, map_natCast]
  field_simp

end GlobalTheory.LvT
end
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwSharp

variable {D : D7} {u : D.what₂.Word}

theorem weight_eq (X Y : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem weightSup_eq (X Y : Ch D u) (τ : D.what₂.Tau) : TauWeight X τ = TauWeight Y τ := by
  unfold TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [weight_eq X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem exponent_eq (X Y : Ch D u) : ETpi X = ETpi Y := by
  unfold ETpi Wt; simp only [weightSup_eq X Y]

theorem tupleChainSharpColumnValuation_of_twisted : ∀ (D : D7) (u : D.what₂.Word) (Tw : TwForms D) (μ : D.what₂.Tup),
    Step0Tie Tw u μ → Conclusion5Sharp (tw Tw u μ) → TupleChainSharpColumnValuation Tw u μ := by
  intro D u Tw μ hT h w hw c n hc hn x hx
  have hw' : OverT (tw Tw u μ) w := hw.trans (Tw.A_T u μ).symm
  have hown : ET (own D u) w = EatT D u w := rfl
  have hE : ET (tw Tw u μ) w = EatT D u w := by
    rw [← hown]; unfold ET
    rw [exponent_eq (tw Tw u μ) (own D u)]
    show (if (Tw.fm u μ).seenP w = true then _ else _) = _
    rw [(hT w hw).1]
  obtain ⟨y, hy, e⟩ := h w hw' c n hc (hE ▸ hn) (Tw.e0 u μ x) ((hT w hw).2 x hx)
  refine ⟨y, hy, e.trans ?_⟩
  show _ • (D.chTw u μ).col ((Tw.fm u μ).emb 0 (Tw.e0 u μ x)) = _
  rw [Tw.embed_mul_block_embedding]

end GlobalTheory.LvT.TwSharp
end
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace GlobalTheory.LvT

variable {D : D7} {u : D.what₂.Word}

theorem natAbs_lamT_le_Wt (X : Ch D u) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j))
    (ha : ¬ (a.1 = 0 ∧ τ ∈ tops D)) : ((PtModel.lamT X j τ).w a).natAbs ≤ Wt X τ := by
  unfold Wt TauWeight
  refine le_trans ?_ (Finset.le_sup (f := fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  refine le_trans ?_ (Finset.le_sup (f := fun a : Fin (D.R.N j) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam j τ).w a - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs) (Finset.mem_univ a))
  rw [if_neg ha]
  exact le_rfl

theorem lamT_last (X : Ch D u) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N (i + 1)))
    (ha : a.1 = D.R.N (i + 1) - 1) : (PtModel.lamT X (i + 1) τ).w a = -X.C.sDiv i τ := by
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  have hm : (i + 1) * (D.R.t + 1) = i * (D.R.t + 1) + D.R.t + 1 := by ring
  have ha' : a.1 = D.R.k + (D.R.t + i * (D.R.t + 1)) := by omega
  have hk : ¬ a.1 < D.R.k := by omega
  have hq : (a.1 - D.R.k) / (D.R.t + 1) = i := by
    rw [ha', Nat.add_sub_cancel_left, Nat.add_mul_div_right _ _ (Nat.succ_pos _),
      Nat.div_eq_of_lt (Nat.lt_succ_self _), zero_add]
  have h1 := X.fm.lam_eq (i + 1) hi τ a
  rw [dif_neg hk] at h1
  simp only [hq] at h1
  have h2 := X.C.sDiv_eq i hi τ
  obtain ⟨c, hc⟩ := D.R.t_odd
  have h3 : (i + 1) * (D.R.t + 1) / 2 = (i + 1) * (c + 1) := by
    have : (i + 1) * (D.R.t + 1) = 2 * ((i + 1) * (c + 1)) := by rw [hc]; ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hcq : (D.R.t : ℚ) = 2 * c + 1 := by exact_mod_cast hc
  change (X.fm.lam (i + 1) τ).w a - (((i + 1) * (D.R.t + 1) / 2 : ℕ) : ℤ) = _
  rw [h3]
  have : (((X.fm.lam (i + 1) τ).w a - (((i + 1) * (c + 1) : ℕ) : ℤ) : ℤ) : ℚ) = ((-X.C.sDiv i τ : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2]
    simp only [wG, sExp, Ranks.N, Nat.add_sub_cancel]
    push_cast
    rw [hcq]
    ring
  exact_mod_cast this

theorem wtBounds_of_nonneg : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u), (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) →
    (∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ) → WtBounds X := by
  intro D u X hb hs
  refine ⟨hb, fun i hi τ => ?_⟩
  have hpos := D.R.N_pos (i + 1)
  have hlast := lamT_last X i hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ rfl
  have hk := D.R.m_add_three_le_k
  have hN : D.R.N (i + 1) = D.R.k + (i + 1) * (D.R.t + 1) := rfl
  refine ⟨hs i hi τ, ?_, ?_, fun hτ => ?_⟩
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨D.R.N (i + 1) - 1, by omega⟩ (fun h => by
      have := h.1
      simp only at this
      omega)
    rw [hlast] at h
    omega
  · unfold DomWeight.detShift
    rw [dif_pos hpos]
    exact hlast
  · have h := natAbs_lamT_le_Wt X (i + 1) hi τ ⟨0, hpos⟩ (fun h => hτ h.2)
    omega

end GlobalTheory.LvT
end

section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section
namespace GlobalTheory.LvT.TwColumn

variable {D : D7} {u : D.what₂.Word}

def WtSigns (X : Ch D u) : Prop :=
  (∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ) ∧ ∀ i, i < D.R.m → ∀ τ, 0 ≤ X.C.sDiv i τ








end GlobalTheory.LvT.TwColumn
end
end
