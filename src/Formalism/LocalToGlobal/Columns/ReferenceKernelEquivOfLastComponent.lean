import Formalism.LocalToGlobal.Columns.RefXi1Above
import Formalism.LocalToGlobal.Columns.ChainOne

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section YA

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def Deco.yOfAt (d : Deco E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) (w : SG) (z : Sp E n) : Prop :=
  (qOf w.1 : E) • z ∈ d.at w.1 ∧ d.be w ((qOf w.1 : E) • z) = v w

theorem Deco.yOfAt_iff {d : Deco E n ST SG} {w : SG} {f : Sp E n ≃ₗ[E] Sp E n} (hf : d.IsLift w f)
    (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) (z : Sp E n) :
    d.yOfAt v w z ↔ ∀ i : Fin n, IntAt w.1 ((qOf w.1 : E) * f.symm z i) ∧ redP w.1 ((qOf w.1 : E) * f.symm z i) = v w i := by
  have e : (qOf w.1 : E) • z = f ((qOf w.1 : E) • f.symm z) := by rw [map_smul, LinearEquiv.apply_symm_apply]
  unfold Deco.yOfAt
  rw [e, hf.1, ciMem_stdAt]
  constructor
  · rintro ⟨h1, h2⟩ i
    refine ⟨h1 i, ?_⟩
    rw [hf.2 _ ((ciMem_stdAt _ _).2 h1)] at h2
    exact congrFun h2 i
  · intro h
    have h1 : ∀ i, IntAt w.1 (((qOf w.1 : E) • f.symm z) i) := fun i => (h i).1
    refine ⟨h1, ?_⟩
    rw [hf.2 _ ((ciMem_stdAt _ _).2 h1)]
    funext i
    exact (h i).2

theorem Deco.yOfAt_sub_iff {d : Deco E n ST SG} {w : SG} (hl : d.HasLift w) (hq2 : ((qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2)
    {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal} {z z' : Sp E n} (hz : d.yOfAt v w z) : d.yOfAt v w z' ↔ z' - z ∈ d.at w.1 := by
  obtain ⟨f, hf⟩ := hl
  have hq := ciQ_mem w.1
  have hq0 : ((qOf w.1 : ℕ) : E) ≠ 0 := ciQ_ne_zero hq2
  rw [Deco.yOfAt_iff hf] at hz ⊢
  have e : z' - z = f (f.symm z' - f.symm z) := by
    rw [map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [e, hf.1, ciMem_stdAt]
  constructor
  · intro h i
    have h1 := ciIntAt_sub (h i).1 (hz i).1
    have h2 : redP w.1 ((qOf w.1 : E) * f.symm z' i - (qOf w.1 : E) * f.symm z i) = 0 := by
      rw [redP_sub (h i).1 (hz i).1, (h i).2, (hz i).2, sub_self]
    have h3 := ciIntAt_div hq hq2 h1 h2
    have e2 : ((qOf w.1 : E) * f.symm z' i - (qOf w.1 : E) * f.symm z i) / (qOf w.1 : E) = f.symm z' i - f.symm z i := by
      field_simp
    rw [e2] at h3
    exact h3
  · intro h i
    have h' : IntAt w.1 (f.symm z' i - f.symm z i) := h i
    have e2 : (qOf w.1 : E) * f.symm z' i = (qOf w.1 : E) * f.symm z i + (qOf w.1 : E) * (f.symm z' i - f.symm z i) := by ring
    rw [e2]
    exact ⟨(ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul h')).2 (hz i).1, by rw [redP_add_natCast_mul hq h']; exact (hz i).2⟩

theorem Deco.yOf_eq_of_mem {d : Deco E n ST SG} (hl : ∀ w, d.HasLift w) (hq2 : ∀ w : SG, ((qOf w.1 : ℕ) : 𝓞 E) ∉ w.1.asIdeal ^ 2)
    {v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal} {z : Sp E n} (hz : z ∈ d.yOf v) : d.yOf v = {z' | ∀ w : SG, z' - z ∈ d.at w.1} := by
  ext z'
  exact forall_congr' fun w => Deco.yOfAt_sub_iff (hl w) (hq2 w) (hz w)

theorem Deco.Ok.exists_beV {d : Deco E n ST SG} (hd : d.Ok) (c : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ x ∈ d.N, ∀ w, d.be w x = c w := by
  classical
  choose x hx hxc using fun w : SG => hd.be_surj w (c w)
  have hcop : Pairwise fun w w' : SG => IsCoprime w.1.asIdeal w'.1.asIdeal := fun w w' hne => by
    show IsCoprime w.1.asIdeal w'.1.asIdeal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne w.1.isMaximal w'.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  choose a ha using fun w₀ : SG => Ideal.exists_forall_sub_mem_ideal hcop fun w : SG => if w = w₀ then (1 : 𝓞 E) else 0
  refine ⟨∑ w₀ : SG, a w₀ • x w₀, Submodule.sum_mem _ fun w₀ _ => Submodule.smul_mem _ _ (hx w₀), fun w => ?_⟩
  rw [hd.be_sum w _ _ fun w₀ _ => le_locP w.1 d.N (Submodule.smul_mem _ _ (hx w₀)), Finset.sum_eq_single w]
  · rw [hd.be_smul w _ _ (le_locP w.1 d.N (hx w)), hxc]
    have h1 := ha w w
    rw [if_pos rfl] at h1
    rw [(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 h1, map_one, one_smul]
  · intro w₀ _ hne
    rw [hd.be_smul w _ _ (le_locP w.1 d.N (hx w₀))]
    have h1 := ha w₀ w
    rw [if_neg (Ne.symm hne), sub_zero] at h1
    rw [Ideal.Quotient.eq_zero_iff_mem.2 h1, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem Deco.Ok.yOf_nonempty {d : Deco E n ST SG} (hd : d.Ok) (G : ℕ) (hG0 : G ≠ 0) (Gw : SG → ℕ) (hG : ∀ w, Gw w * qOf w.1 = G)
    (hGw : ∀ w : SG, ((Gw w : ℕ) : 𝓞 E) ∉ w.1.asIdeal) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) : ∃ y, y ∈ d.yOf v := by
  obtain ⟨x, hx, hxc⟩ := hd.exists_beV fun w => Ideal.Quotient.mk w.1.asIdeal ((Gw w : ℕ) : 𝓞 E) • v w
  refine ⟨(G : E)⁻¹ • x, fun w => ?_⟩
  have hGE : (G : E) ≠ 0 := by exact_mod_cast hG0
  have e : ((Gw w : ℕ) : 𝓞 E) • ((qOf w.1 : E) • ((G : E)⁻¹ • x)) = x := by
    rw [← algebraMap_smul E (((Gw w : ℕ) : 𝓞 E)), map_natCast, smul_smul, smul_smul, ← Nat.cast_mul, hG w, mul_inv_cancel₀ hGE, one_smul]
  have hmem : (qOf w.1 : E) • ((G : E)⁻¹ • x) ∈ d.at w.1 := (mem_locP w.1 d.N _).2 ⟨_, hGw w, by rw [e]; exact hx⟩
  refine ⟨hmem, ?_⟩
  have h1 := hd.be_smul w ((Gw w : ℕ) : 𝓞 E) _ hmem
  rw [e, hxc w] at h1
  funext i
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_left_cancel₀ (mk_ne_zero (hGw w)) h2).symm

end YA

section YB

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

variable {sel mu} in
theorem pc_rowSG (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (P : rowSG Pr sel mu) : P.1 ∈ Pr.vGs := by
  classical
  rcases Finset.mem_union.1 P.2 with h | h
  · exact h
  · exact absurd (hQ ▸ h : P.1 ∈ (∅ : Finset (HeightOneSpectrum (𝓞 X.E)))) (Finset.notMem_empty _)

variable {sel mu cst} in
open Classical in

theorem pc_mem_locLat_zero (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : Sp X.E n) :
    v ∈ locLat (rowSG Pr sel mu) N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) ↔ ∀ w : Pr.vGs, v ∈ localization₂ w.1.asIdeal N := by
  classical
  rw [mem_locLat]
  constructor
  · intro h w
    have h1 := h ⟨w.1, Finset.mem_union_left _ w.2⟩
    rw [if_pos w.2, zpow_zero, inv_one, one_smul] at h1
    exact h1
  · intro h P
    rw [if_pos (hQ P), zpow_zero, inv_one, one_smul]
    exact h ⟨P.1, hQ P⟩

theorem pc_G_notMem (hPr : Pr.Ok) {i j : Fin 2} (hij : i ≠ j) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g j : ℕ) : 𝓞 X.E) ∉ w.asIdeal := by
  intro h
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
    rw [← ciQOf_eq hPr hw]
    exact ciQ_mem w
  have hne : Pr.g i ≠ Pr.g j := by
    intro e
    apply hPr.g_ne
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact e | exact e.symm
  have hc : Nat.Coprime (Pr.g i) (Pr.g j) := (Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hc)
  have h2 : ((a : ℤ) : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) + ((b : ℤ) : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 X.E) hab
    push_cast at this
    exact this
  exact one_notMem w (h2 ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h))

theorem yOf_nonempty (hPr : Pr.Ok) {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} {d : Deco X.E n ST Pr.vGs} (hd : d.Ok)
    (v : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal) : ∃ y, y ∈ d.yOf v := by
  classical
  refine hd.yOf_nonempty (Pr.g 0 * Pr.g 1) (Nat.mul_ne_zero (hPr.g_prime 0).ne_zero (hPr.g_prime 1).ne_zero)
    (fun w => if w.1 ∈ Pr.vG 0 then Pr.g 1 else Pr.g 0) (fun w => ?_) (fun w => ?_) v
  · by_cases h0 : w.1 ∈ Pr.vG 0
    · simp only [if_pos h0]
      rw [ciQOf_eq hPr h0, mul_comm]
    · have h1 : w.1 ∈ Pr.vG 1 := (Finset.mem_union.1 w.2).resolve_left h0
      simp only [if_neg h0]
      rw [ciQOf_eq hPr h1]
  · by_cases h0 : w.1 ∈ Pr.vG 0
    · simp only [if_pos h0]
      exact pc_G_notMem hPr (by decide) h0
    · have h1 : w.1 ∈ Pr.vG 1 := (Finset.mem_union.1 w.2).resolve_left h0
      simp only [if_neg h0]
      exact pc_G_notMem hPr (by decide) h1

theorem yOf_mem_ybSet (hX : X.Ok) (hPr : Pr.Ok) (hQ : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs) {n : ℕ}
    {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST Pr.vGs) (v : ∀ w : Pr.vGs, Fin n → 𝓞 X.E ⧸ w.1.asIdeal) :
    d.1.yOf v ∈ ybSet sel mu cst d.1.N := by
  classical
  obtain ⟨y, hy⟩ := yOf_nonempty hPr d.2 v
  refine ⟨y, ?_, ?_⟩
  · rw [mem_locLat]
    intro P
    rw [if_pos (hQ P), _root_.zpow_neg, zpow_one, inv_inv]
    exact (hy ⟨P.1, hQ P⟩).1
  · rw [Deco.yOf_eq_of_mem (fun w => d.2.hasLift w) (fun w => ciQ_notMem_sq hX hPr w.2) hy]
    ext z
    exact (pc_mem_locLat_zero (cst := cst) hQ d.1.N (z - y)).symm

end YB

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Eq

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (m2 : ℕ) (Am : Amb X) (u : Pr.Word)

def oneAl (j : ℕ) (h : j ≤ m2 + 1) : (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2).β j := ⟨(), h⟩

def oneG {j : ℕ} (g : FormG (Λ j)) : FrmG (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) := (g.1, g.2, 1)

variable {Λ sel mu}

theorem liftQ_oneG {j : ℕ} (g : FormG (Λ j)) (p : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    (liftQ hQ ((formAct (Λ j)).toSMul.smul g p) : ChPt (R := R) sel mu u j) =
      (frmAct (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))).toSMul.smul (oneG Λ sel mu g) (liftQ hQ p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · funext ⟨P, hP⟩
    rw [hQ] at hP
    simp at hP

theorem frmRho_oneG {j : ℕ} (g : FormG (Λ j)) :
    frmRho (colValF W sel mu u j) (Λ j) (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))) (oneG Λ sel mu g) =
      formRho (colVal W u j (Pr.vT u) Pr.vGs) (Λ j) g := by
  show (((Λ j).chr g.2 * (LevQFam.top X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))).chr 1 : X.Kˣ) : X.K) •
      (colVal W u j (Pr.vT u) Pr.vGs).rho g.1 =
    (((Λ j).chr g.2 : X.Kˣ) : X.K) • (colVal W u j (Pr.vT u) Pr.vGs).rho g.1
  rw [map_one, mul_one]

variable (Λ sel mu)

def FixE : Prop :=
  ∀ h ∈ (Λ (m2 + 1)).grp, ∀ w : Pr.vGs,
    ((h w : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal)) : Matrix _ _ (𝓞 X.E ⧸ w.1.asIdeal)).mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k

def RefKEquiv (i : ℕ) : Prop :=
  ∀ (g : FormG (Λ i)) (g' : FormG (Λ (i + 1))) (p : DecoSet X.E (R.N i) (Pr.vT u) Pr.vGs) (p' : DecoSet X.E (R.N (i + 1)) (Pr.vT u) Pr.vGs),
    refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i
        (liftQ hQ ((formAct (Λ i)).toSMul.smul g p)) (liftQ hQ ((formAct (Λ (i + 1))).toSMul.smul g' p')) =
      (formRho (colVal W u (i + 1) (Pr.vT u) Pr.vGs) (Λ (i + 1)) g') ∘ₗ
        (refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i (liftQ hQ p) (liftQ hQ p')) ∘ₗ
          (formRho (colVal W u i (Pr.vT u) Pr.vGs) (Λ i) g⁻¹)

variable {W Λ Ch sel mu cst hQ m2 Am u}

theorem xiEquiv_of_refK (h : ∀ i, RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i) :
    XiEquiv W Λ Ch sel mu cst Am u
      (refXi1 Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) hQ m2 (oneAl Λ sel mu m2) u) := by
  unfold XiEquiv refXi1
  intro a
  unfold ClsEq xiKer XiRef
  intro g g' p p'
  exact h a g g' p p'

theorem refKEquiv_of_mat {i : ℕ} (hi : i < m2)
    (hM : MatEquiv W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i := by
  intro g g' p p'
  have e : ∀ (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i q q' =
        matK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) i
          (oneAl Λ sel mu m2 i (by omega)) (oneAl Λ sel mu m2 (i + 1) (by omega)) q q' := by
    intro q q'
    unfold refK matK
    congr 1
    funext x
    unfold XiRef
    rw [dif_pos hi]
  rw [e, e, liftQ_oneG, liftQ_oneG]
  have h := hM i hi (oneAl Λ sel mu m2 i (by omega)) (oneAl Λ sel mu m2 (i + 1) (by omega)) (oneG Λ sel mu g) (oneG Λ sel mu g')
    (liftQ hQ p) (liftQ hQ p')
  refine h.trans ?_
  have h1 := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2 := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (i + 1)) (Λ (i + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u i) (Λ i) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1, h2]
  rfl

theorem lastVectorLine_equivariant (hF : FixE (R := R) Λ m2) (g' : FormG (Λ (m2 + 1))) (p' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs) :
    ((formAct (Λ (m2 + 1))).toSMul.smul g' p').1.y0 R.k = (fun v => g'.1.1 v) '' (p'.1.y0 R.k) := by
  unfold FixE at hF
  have hact : ((formAct (Λ (m2 + 1))).toSMul.smul g' p').1 = Deco.act ↑g'.1 ↑g'.2 p'.1 := rfl
  have hloc : ∀ (P : HeightOneSpectrum (𝓞 X.E)) (y : _),
      y ∈ (Deco.act ↑g'.1 ↑g'.2 p'.1).at P ↔ g'.1.1.symm y ∈ p'.1.at P := by
    intro P y
    change (∃ s ∈ P.asIdeal.primeCompl, s • y ∈ gmap g'.1.1 p'.1.N) ↔
      (∃ s ∈ P.asIdeal.primeCompl, s • g'.1.1.symm y ∈ p'.1.N)
    constructor
    · rintro ⟨s, hs, hy⟩
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      refine ⟨s, hs, ?_⟩
      have e1 : g'.1.1.symm (s • y) = s • g'.1.1.symm y :=
        (g'.1.1.symm.toLinearMap.restrictScalars (𝓞 X.E)).map_smul s y
      rw [← e1, ← hzy]
      simpa using hz
    · rintro ⟨s, hs, hy⟩
      refine ⟨s, hs, Submodule.mem_map.mpr ⟨_, hy, ?_⟩⟩
      have e1 : g'.1.1 (s • g'.1.1.symm y) = s • g'.1.1 (g'.1.1.symm y) :=
        (g'.1.1.toLinearMap.restrictScalars (𝓞 X.E)).map_smul s _
      simpa using e1
  have hbe : ∀ (w : Pr.vGs) (y : _),
      (Deco.act ↑g'.1 ↑g'.2 p'.1).be w y = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k ↔
        p'.1.be w (g'.1.1.symm y) = Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k := by
    intro w y
    have hM := hF g'.2.1 g'.2.2 w
    change (g'.2.1 w).1.mulVec (p'.1.be w (g'.1.1.symm y)) = _ ↔ _
    generalize p'.1.be w (g'.1.1.symm y) = z
    constructor
    · intro hz
      calc z = ((g'.2.1 w)⁻¹).1.mulVec ((g'.2.1 w).1.mulVec z) := by
            rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
        _ = ((g'.2.1 w)⁻¹).1.mulVec ((g'.2.1 w).1.mulVec
              (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N (m2 + 1)) R.k)) := by
            rw [hz, hM]
        _ = _ := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · rintro rfl
      exact hM
  rw [hact]
  ext v
  simp only [Deco.y0, Deco.yOf, Set.mem_image, Set.mem_setOf_eq, Nat.cast_smul_eq_nsmul]
  constructor
  · intro H
    refine ⟨g'.1.1.symm v, fun w => ?_, by simp⟩
    obtain ⟨h1, h2⟩ := H w
    rw [hloc, map_nsmul] at h1
    rw [hbe, map_nsmul] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨x, hx, rfl⟩ w
    obtain ⟨h1, h2⟩ := hx w
    rw [hloc, hbe, map_nsmul, LinearEquiv.symm_apply_apply]
    exact ⟨h1, h2⟩

theorem referenceKernelEquiv_of_lastComponent (hX : X.Ok) (hPr : Pr.Ok) (hF : FixE (R := R) Λ m2)
    (hY : YbHyp (R := R) sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) u m2 (oneAl Λ sel mu m2 (m2 + 1) le_rfl))
    (h1 : Cp1EquivOn W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
      (oneAl Λ sel mu m2 (m2 + 1) le_rfl) hY) :
    RefKEquiv W Λ Ch sel mu cst hQ m2 Am u m2 := by
  intro g g' p p'
  have hmem : ∀ q' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs, q'.1.y0 R.k ∈ ybSet sel mu cst q'.1.N :=
    fun q' => yOf_mem_ybSet sel mu cst hX hPr (pc_rowSG hQ) q' _
  have e : ∀ (q : ChPt (R := R) sel mu u m2) (q' : DecoSet X.E (R.N (m2 + 1)) (Pr.vT u) Pr.vGs),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) m2 q (liftQ hQ q') =
        cp1K W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2)
          (oneAl Λ sel mu m2 m2 (by omega)) q (liftQ hQ q') (q'.1.y0 R.k) := by
    intro q q'
    unfold refK cp1K
    rw [if_pos (show q'.1.y0 R.k ∈ ybSet sel mu cst (liftQ hQ q' : ChPt (R := R) sel mu u (m2 + 1)).deco.1.N from hmem q')]
    congr 1
    funext x
    unfold XiRef
    rw [dif_neg (lt_irrefl _), dif_pos rfl]
    rfl
  rw [e, e, lastVectorLine_equivariant hF, liftQ_oneG, liftQ_oneG]
  have h := h1 (oneAl Λ sel mu m2 m2 (by omega)) (oneG Λ sel mu g) (oneG Λ sel mu g') (liftQ hQ p) (liftQ hQ p') (p'.1.y0 R.k) (hmem p')
  refine h.trans ?_
  have h1' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g'
  have h2' := frmRho_oneG (W := W) (u := u) (sel := sel) (mu := mu) g⁻¹
  show (frmRho (colValF W sel mu u (m2 + 1)) (Λ (m2 + 1)) _ (oneG Λ sel mu g')) ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u m2) (Λ m2) _ (oneG Λ sel mu g)⁻¹) = _
  have h3 : (oneG Λ sel mu g)⁻¹ = oneG Λ sel mu g⁻¹ := by
    unfold oneG
    simp
  rw [h3, h1', h2']
  rfl

theorem refKEquiv_above {i : ℕ} (hi : m2 + 1 < i) : RefKEquiv W Λ Ch sel mu cst hQ m2 Am u i := by
  intro g g' p p'
  have e : ∀ (q : ChPt (R := R) sel mu u i) (q' : ChPt (R := R) sel mu u (i + 1)),
      refK W Ch sel mu cst (oneIdx Λ (QE sel (mu : Chr X.F X.E X.K)) m2) (chTh W Ch sel mu cst Am u m2) (oneAl Λ sel mu m2) i q q' = 0 := by
    intro q q'
    unfold refK
    refine kerOf_zero _ _ _ _ _ _ _ _ _ fun x => ?_
    unfold XiRef
    rw [dif_neg (by omega), dif_neg (by omega), if_neg (by omega)]
  rw [e, e]
  ext x
  exact (map_zero (formRho (colVal W u (i + 1) (Pr.vT u) Pr.vGs) (Λ (i + 1)) g')).symm ▸ rfl

end Eq

end Formalism.L2.Col
end
end
