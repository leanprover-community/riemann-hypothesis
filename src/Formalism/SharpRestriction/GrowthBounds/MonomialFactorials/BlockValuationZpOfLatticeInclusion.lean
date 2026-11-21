import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockBoundUniformiser

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem goodCount_mem (p : ℕ) [Fact p.Prime] {Vs : Type} [AddCommGroup Vs] [Module ℤ_[p] Vs]
    (be : Vs → Vs → ℚ_[p]) (L : Submodule ℤ_[p] Vs) (D : ℤ) :
    ∃ x y : Fin (goodCount p be L D) → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
      ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0 := by
  set S : Set ℕ := {n | ∃ x y : Fin n → Vs, (∀ i, x i ∈ L) ∧ (∀ i, y i ∈ L) ∧
    ∀ i j, be (x i) (y j) = if i = j then (p : ℚ_[p]) ^ D else 0} with hS
  have h0 : (0 : ℕ) ∈ S := ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hmem : sSup S ∈ S := by
    by_cases hb : BddAbove S
    · exact Nat.sSup_mem ⟨0, h0⟩ hb
    · rw [Nat.sSup_of_not_bddAbove hb]; exact h0
  exact hmem

section Lin

variable {k σ : Type} [Field k] {r : ℕ}

theorem harmonicProjection_add (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (y y' : MvPolynomial σ k) :
    tieP w e zv sv o n z (y + y') = tieP w e zv sv o n z y + tieP w e zv sv o n z y' := by
  unfold tieP
  simp only [mul_add, map_add, smul_add, Finset.sum_add_distrib]

theorem harmonicProjection_smul (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k) (y : MvPolynomial σ k) :
    tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by
  unfold tieP
  simp only [mul_smul_comm, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun l _ => smul_comm _ _ _

end Lin

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem Pall_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (u + v) = G.Pall p (r := r) j jp u + G.Pall p (r := r) j jp v := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_add]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_add]

theorem Pall_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    G.Pall p (r := r) j jp (c • u) = c • G.Pall p (r := r) j jp u := by
  unfold M.BlockData.Pall
  rw [← harmonicProjection_smul]
  congr 1
  induction (List.finRange G.T.t) with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons]; rw [ih, harmonicProjection_smul]

def Th (j : Fin G.T.t → ℕ) (jp : ℕ) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : MvPolynomial (M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp * G.Pall p (r := r) j jp u

theorem Th_add (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (u + v) = Th p G j jp u + Th p G j jp v := by
  unfold Th; rw [Pall_add, mul_add]

theorem Th_smul (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) :
    Th p G j jp (c • u) = c • Th p G j jp u := by
  unfold Th; rw [Pall_smul, mul_smul_comm]

theorem Th_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : Th p (r := r) G j jp (0 : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) = 0 := by
  have := Th_smul p (r := r) G j jp 0 0
  simpa using this

theorem zsmul_eq (c : ℤ_[p]) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) : c • u = (c : ℚ_[p]) • u :=
  (algebraMap_smul ℚ_[p] c u).symm

theorem Th_mem_PSZ (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (u : MvPolynomial (M.BVar N r G.T.t) ℚ_[p])
    (hu : u ∈ Ljj p (r := r) G j jp) : Th p G j jp u ∈ G.PSZ p (r := r) := by
  unfold Ljj at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    apply Submodule.subset_span
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hl, y, hy, g, hg, rfl⟩
  | zero => rw [Th_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Th_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [zsmul_eq, Th_smul, ← zsmul_eq]; exact Submodule.smul_mem _ c hx

def lvC (j : Fin G.T.t → ℕ) (jp : ℕ) : ℕ :=
  ((∏ i, (j i).factorial) * jp.factorial) ^ 2 *
    ((∏ i, (((G.lettersAt j jp).deg (G.letterAt (G.T.pos i)) +
        (G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)) + r + G.T.z i + 1 + j i - 1).choose (j i) *
      (G.T.z i).factorial)) *
    (((G.LL.deg G.uPos - jp) + (G.B - jp) + r + G.zPlus + 1 + jp - 1).choose jp * G.zPlus.factorial))

theorem Th_fock (hB : G.BlockOK) (hr : 1 ≤ r) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp)
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j jp) :
    fockK (Th p G j jp u) (Th p G j jp v) = (lvC (r := r) G j jp : ℚ_[p]) * fockK u (G.phiAll p (r := r) j jp v) := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      have h := (fock_block_decomposition p N r G hB hr).2 j jp hl y hy.1 y' hy'.1 g hg g' hg'
      rw [fockK_smul_left, fockK_smul_right] at h
      have hf : ((∏ i, ((j i).factorial : ℚ_[p])) * (jp.factorial : ℚ_[p])) ≠ 0 :=
        mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      unfold Th lvC
      push_cast
      push_cast at h
      have hf2 : (∏ i, ((j i).factorial : ℚ_[p])) ^ 2 * (jp.factorial : ℚ_[p]) ^ 2 ≠ 0 := by
        rw [← mul_pow]; exact pow_ne_zero 2 hf
      field_simp at h
      rw [div_eq_iff hf2] at h
      rw [h]
      ring
    | zero => rw [Th_zero, fockK_zero_right, map_zero, fockK_zero_right, mul_zero]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, map_add, fockK_add_right, mul_add]
    | smul c a _ ha =>
      rw [zsmul_eq, Th_smul, fockK_smul_right, ha, map_smul, fockK_smul_right]; ring
  | zero => rw [Th_zero, fockK_zero_left, fockK_zero_left, mul_zero]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, fockK_add_left, mul_add]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, fockK_smul_left]; ring

theorem Th_orth (hB : G.BlockOK) (hr : 1 ≤ r) (j j' : Fin G.T.t → ℕ) (jp jp' : ℕ) (hl : G.LevelOK j jp)
    (hl' : G.LevelOK j' jp') (hne : (j, jp) ≠ (j', jp'))
    (u v : MvPolynomial (M.BVar N r G.T.t) ℚ_[p]) (hu : u ∈ Ljj p (r := r) G j jp) (hv : v ∈ Ljj p (r := r) G j' jp') :
    fockK (Th p G j jp u) (Th p G j' jp' v) = 0 := by
  unfold Ljj at hu hv
  induction hu using Submodule.span_induction with
  | mem x hx =>
    induction hv using Submodule.span_induction with
    | mem x' hx' =>
      obtain ⟨y, hy, g, hg, rfl⟩ := hx
      obtain ⟨y', hy', g', hg', rfl⟩ := hx'
      exact (fock_block_decomposition p N r G hB hr).1 j j' jp jp' hl hl' hne y hy.1 y' hy'.1 g hg g' hg'
    | zero => rw [Th_zero, fockK_zero_right]
    | add a b _ _ ha hb => rw [Th_add, fockK_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_right, ha, mul_zero]
  | zero => rw [Th_zero, fockK_zero_left]
  | add a b _ _ ha hb => rw [Th_add, fockK_add_left, ha, hb, add_zero]
  | smul c a _ ha => rw [zsmul_eq, Th_smul, fockK_smul_left, ha, mul_zero]

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.ProjS

theorem exists_scal (p : ℕ) [hp : Fact p.Prime] (m Mx : ℕ) (hm : m ≠ 0) (h : padicValNat p m ≤ Mx) :
    ∃ c : ℤ_[p], (c : ℚ_[p]) * (m : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
  have hm' : (m : ℚ_[p]) ≠ 0 := by exact_mod_cast hm
  have hn : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hm', Padic.valuation_natCast]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  refine ⟨⟨(p : ℚ_[p]) ^ Mx / m, ?_⟩, ?_⟩
  · rw [norm_div, norm_pow, Padic.norm_p, hn, div_le_one (zpow_pos hp0 _), inv_pow, ← zpow_natCast, ← zpow_neg]
    exact zpow_le_zpow_right₀ hp1 (by omega)
  · show (p : ℚ_[p]) ^ Mx / m * m = _
    field_simp

section Block

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def expU (a : ℕ) : ℕ := (G.T.t + 1) * ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊

def expM : ℕ := (levels G).sup fun l => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)

theorem lvC_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : lvC (r := r) G j jp ≠ 0 := by
  unfold lvC
  refine mul_ne_zero (pow_ne_zero 2 (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _)
    (Nat.factorial_ne_zero _))) (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero ?_
      (Nat.factorial_ne_zero _)) (mul_ne_zero ?_ (Nat.factorial_ne_zero _)))
  · exact (Nat.choose_pos (by omega)).ne'
  · exact (Nat.choose_pos (by omega)).ne'

theorem degFact_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : degFact G j jp ≠ 0 := by
  unfold degFact
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)

def nLv (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) : ℕ :=
  goodCount p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D

theorem nLv_mem (D : ℤ) (l : (Fin G.T.t → ℕ) × ℕ) :
    ∃ x y : Fin (nLv p (r := r) G D l) → MvPolynomial (M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G l.1 l.2) ∧ (∀ i, y i ∈ Ljj p (r := r) G l.1 l.2) ∧
      ∀ i j, fockK (G.phiAll p (r := r) l.1 l.2 (x i)) (y j) =
        (if i = j then (p : ℚ_[p]) ^ D else 0) * (degFact G l.1 l.2 : ℚ_[p]) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p (bejj p (r := r) G l.1 l.2) (Ljj p (r := r) G l.1 l.2) D
  refine ⟨x, y, hx, hy, fun i j => ?_⟩
  have hd : (degFact G l.1 l.2 : ℚ_[p]) ≠ 0 := by exact_mod_cast degFact_ne_zero G _ _
  have h := hxy i j
  unfold bejj at h
  rw [div_eq_iff hd] at h
  exact h

theorem blkZ_gen (hB : G.BlockOK) (hr : 1 ≤ r) (U Mx : ℕ)
    (hLL : ∀ x ∈ G.PSZ p (r := r), ((p : ℚ_[p]) ^ U) • x ∈ G.SSZ p (r := r))
    (hM : ∀ l ∈ levels G, padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ Mx) (D : ℤ) :
    ∃ (n : ℕ) (x y : Fin n → MvPolynomial (M.BVar N r G.T.t) ℚ_[p]),
      (∀ i, x i ∈ G.SSZ p (r := r)) ∧ (∀ i, y i ∈ G.SSZ p (r := r)) ∧
      (∀ i j, fockK (x i) (y j) =
        if i = j then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0) ∧
      ∑ l ∈ levels G, Module.finrank ℤ_[p] (Ljj p (r := r) G l.1 l.2) ≤
        n + ∑ l ∈ levels G, badLvl p (r := r) G l.1 l.2 D := by
  classical
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hw := fun l : (Fin G.T.t → ℕ) × ℕ => nLv_mem p (r := r) G D l
  choose u v hu hv huv using hw
  have hsc : ∀ l : ↥(levels G), ∃ c : ℤ_[p],
      (c : ℚ_[p]) * ((lvC (r := r) G l.1.1 l.1.2 * degFact G l.1.1 l.1.2 : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ Mx := by
    intro l
    exact exists_scal p _ Mx (mul_ne_zero (lvC_ne_zero G _ _) (degFact_ne_zero G _ _)) (hM l.1 l.2)
  choose sc hsc' using hsc
  have hok : ∀ l : ↥(levels G), G.LevelOK l.1.1 l.1.2 := fun l => (Finset.mem_filter.1 l.2).2
  let I := Σ l : ↥(levels G), Fin (nLv p (r := r) G D l.1)
  let Xf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a => ((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (v a.1.1 a.2)
  let Yf : I → MvPolynomial (M.BVar N r G.T.t) ℚ_[p] := fun a =>
    sc a.1 • (((p : ℚ_[p]) ^ U) • Th p G a.1.1.1 a.1.1.2 (u a.1.1 a.2))
  have hX : ∀ a, Xf a ∈ G.SSZ p (r := r) := fun a => hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hv _ _))
  have hY : ∀ a, Yf a ∈ G.SSZ p (r := r) := fun a =>
    Submodule.smul_mem _ _ (hLL _ (Th_mem_PSZ p G _ _ (hok a.1) _ (hu _ _)))
  have hXY : ∀ a b : I, fockK (Xf a) (Yf b) = if a = b then (p : ℚ_[p]) ^ (D + 2 * (U : ℤ) + (Mx : ℤ)) else 0 := by
    rintro ⟨l, i⟩ ⟨l', k⟩
    simp only [Xf, Yf]
    rw [zsmul_eq, fockK_smul_left, fockK_smul_right, fockK_smul_right]
    by_cases hll : l = l'
    · subst hll
      rw [Th_fock p G hB hr _ _ (hok l) _ _ (hv _ _) (hu _ _), fockK_symm]
      have h1 := huv l.1 k i
      have h2 := hsc' l
      push_cast at h2
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl] at h1
        rw [h1, if_pos rfl]
        rw [zpow_add₀ hp0, zpow_add₀ hp0, zpow_natCast, ← h2, two_mul, zpow_add₀ hp0, zpow_natCast]
        ring
      · rw [if_neg (fun h => hik h.symm)] at h1
        rw [h1, if_neg]
        · ring
        · intro h
          rw [Sigma.mk.inj_iff] at h
          exact hik (eq_of_heq h.2)
    · have hne : (l.1.1, l.1.2) ≠ (l'.1.1, l'.1.2) := by
        intro h
        exact hll (Subtype.ext h)
      rw [Th_orth p G hB hr _ _ _ _ (hok l) (hok l') hne _ _ (hv _ _) (hu _ _), if_neg]
      · ring
      · intro h
        rw [Sigma.mk.inj_iff] at h
        exact hll h.1
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, fun i => Xf (e.symm i), fun i => Yf (e.symm i), fun i => hX _, fun i => hY _, ?_, ?_⟩
  · intro i j
    rw [hXY]
    simp only [e.symm.injective.eq_iff]
  · have hc : Fintype.card I = ∑ l ∈ levels G, nLv p (r := r) G D l := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      exact Finset.sum_coe_sort (levels G) (nLv p (r := r) G D)
    rw [hc, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun l _ => ?_
    unfold badLvl bad nLv
    exact le_add_tsub

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem le_expM (l : (Fin G.T.t → ℕ) × ℕ) (hl : l ∈ levels G) :
    padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ expM p (r := r) G :=
  Finset.le_sup (f := fun l : (Fin G.T.t → ℕ) × ℕ => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)) hl

theorem levels_nonempty : (levels G).Nonempty := by
  classical
  refine ⟨(fun _ => 0, 0), ?_⟩
  unfold levels
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨⟨fun _ => Finset.mem_range.2 (Nat.succ_pos _), Finset.mem_range.2 (Nat.succ_pos _)⟩,
    fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _⟩

theorem exists_expM : ∃ l ∈ levels G, expM p (r := r) G = padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) :=
  Finset.exists_mem_eq_sup (levels G) (levels_nonempty G)
    (fun l : (Fin G.T.t → ℕ) × ℕ => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2))

end Gen

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def aBig : ℕ := (3 * X.s + 2) * X.L.a

def RestLL : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ x ∈ (gB C0 CE1 CE2 X aTop aPlus b).PSZ X.p (r := X.r),
        ((X.p : ℚ_[X.p]) ^ (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X))) • x ∈
          (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r)

def RestVal : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ l ∈ levels (gB C0 CE1 CE2 X aTop aPlus b),
        ∀ z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r), ∀ μ ∈ z.support,
          (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
              degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) +
            2 * (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
          (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + levelPassageLoss X

theorem lv_eq (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    lv C0 CE1 CE2 X aTop b = levels (gB C0 CE1 CE2 X aTop aPlus b) := rfl

theorem gB_blockOK (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    (gB C0 CE1 CE2 X aTop aPlus b).BlockOK := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i i' h
    have h' : (i : ℕ) < (i' : ℕ) := h
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) < 2 * ((X.S C0 CE1 CE2).sigma + (i' : ℕ))
    omega
  · intro i
    have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := (uTop (X.S C0 CE1 CE2) i).2
    refine ⟨?_, ?_, ?_⟩
    · show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 < 2 * X.s + 1
      omega
    · show decide ((2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ))) % 2 = 0) = true
      simp
    · show decide ((2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) % 2 = 0) = false
      rw [decide_eq_false_iff_not]
      omega
  · intro i
    have hi : (i : ℕ) < (X.S C0 CE1 CE2).t := i.2
    refine ⟨(⟨(i : ℕ), Nat.lt_succ_of_lt hi⟩ : Fin ((X.S C0 CE1 CE2).t + 1)), ?_⟩
    show (if h : (i : ℕ) < (X.S C0 CE1 CE2).t then 2 * (uTop (X.S C0 CE1 CE2) ⟨(i : ℕ), h⟩ : ℕ) + 1 else 2 * X.s + 1) =
      2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1
    rw [dif_pos hi]
    rfl
  · intro i
    have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := (uTop (X.S C0 CE1 CE2) i).2
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 < 2 * X.s
    omega
  · show decide ((2 * X.s) % 2 = 0) = true
    simp
  · rfl

theorem block_valuation_Zp_of_lattice_inclusion (hr : 1 ≤ X.r) (hLL : RestLL C0 CE1 CE2 X) (hV : RestVal C0 CE1 CE2 X) :
    BlockBoundIntegers C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK D _
  obtain ⟨n, x, y, hx, hy, hxy, hsum⟩ := blkZ_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)
    (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X))
    (expM X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)) (hLL aTop hT aPlus hP b hK)
    (fun l hl => le_expM X.p _ l hl) D
  refine ⟨n, x, y, _, hx, hy, hxy, ?_, hsum⟩
  intro z hz μ hμ
  obtain ⟨l, hl, hl'⟩ := exists_expM X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)
  have h := hV aTop hT aPlus hP b hK l hl z hz μ hμ
  rw [← hl'] at h
  push_cast
  linarith

theorem gB_deg_le {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (aTop : Fin X.s → ℕ)
    (haTop : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (aPlus : ℕ) (haPlus : aPlus ∈ X.winA)
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) aTop b) :
    1 ≤ aBig X ∧ (∀ x, (gB C0 CE1 CE2 X aTop aPlus b).LL.deg x ≤ 2 * aBig X) ∧
      (gB C0 CE1 CE2 X aTop aPlus b).B ≤ 2 * aBig X ∧
      (∀ i, (gB C0 CE1 CE2 X aTop aPlus b).T.z i ≤ 2 * aBig X) ∧
      (gB C0 CE1 CE2 X aTop aPlus b).zPlus ≤ 2 * aBig X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : 1 ≤ X.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have ha0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have hb10 : 5 / 2 * X.L.b' ≤ (X.L.a : ℝ) / 10 := by nlinarith [hF.b_lt, hF.b0]
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have h4 : (0 : ℝ) ≤ X.L.Q := by show (0 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'; positivity
    positivity
  have hLa : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 := by
    show X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2 ≤ 1
    have h1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hF.La_lt]
    have h2 : 4 / (X.L.p : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hbig : ((2 * aBig X : ℕ) : ℝ) = 2 * ((3 * (X.s : ℝ) + 2) * (X.L.a : ℝ)) := by
    unfold aBig; push_cast; ring
  have hsa : 0 ≤ (X.s : ℝ) * (X.L.a : ℝ) := mul_nonneg hs0 ha0
  have hwin : ∀ x ∈ X.winA, (x : ℝ) ≤ 2 * (X.L.a : ℝ) := by
    intro x hx
    have h2 := (Finset.mem_Icc.1 hx).2
    have h3 : (x : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
    exact (h3.trans (Nat.floor_le hF.win0)).trans hF.win_le
  have hbT : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ (X.L.a : ℝ) / 10 := fun i =>
    (hF.bT_le _ (segPos_mem X.L.TT X.j i)).trans hb10
  have hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ (X.L.a : ℝ) / 10 := (hF.bT_le _ (segNext_mem X.L.TT X.j)).trans hb10
  refine ⟨?_, fun x => ?_, ?_, fun i => ?_, ?_⟩
  · have h1 : 1 ≤ X.L.a := by exact_mod_cast hF.a1
    unfold aBig
    exact Nat.mul_pos (by omega) h1
  · have h1 := segChain_deg_le (X.S C0 CE1 CE2) aTop b hK hp1 hE0 hF.La0 hLa (2 * (X.L.a : ℝ)) ((X.L.a : ℝ) / 10)
      hbT hbP (fun i => hwin _ (Fintype.mem_piFinset.1 haTop i))
      (show (X.L.a : ℝ) ≤ 2 * (X.L.a : ℝ) by linarith) x
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).LL.deg x : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans h1 ?_
      nlinarith
    exact_mod_cast h2
  · have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).B : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans hbP ?_
      nlinarith
    exact_mod_cast h2
  · have h0 : (gB C0 CE1 CE2 X aTop aPlus b).T.z i ≤ (X.S C0 CE1 CE2).bTop (uTop (X.S C0 CE1 CE2) i) :=
      (Nat.sub_le _ _).trans (coarseA_le (X.S C0 CE1 CE2) b _)
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).T.z i : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans (Nat.cast_le.2 h0) (le_trans (hbT _) ?_)
      nlinarith
    exact_mod_cast h2
  · have h0 : (gB C0 CE1 CE2 X aTop aPlus b).zPlus ≤ aPlus := Nat.sub_le _ _
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).zPlus : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans (Nat.cast_le.2 h0) (le_trans (hwin _ haPlus) ?_)
      nlinarith
    exact_mod_cast h2

theorem restLL_of {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hTU : ∀ (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r),
      Formalism.InvariantFactorPaths.KP.LL.HypJoin X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) ∧
      Formalism.InvariantFactorPaths.KP.LL.HypU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)) : RestLL C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK
  obtain ⟨h1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hr : 1 ≤ X.r := by have := r_ge C0 CYb Cde Ck CD Cb Cc X hH; omega
  exact (Formalism.InvariantFactorPaths.KP.Top.levelLattice X.p (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b) (aBig X)
    (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr h1 h2 h3 h4 h5 (hTU aTop aPlus b).1 (hTU aTop aPlus b).2).2.2

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
