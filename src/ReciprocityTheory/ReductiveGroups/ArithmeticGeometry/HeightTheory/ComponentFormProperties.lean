import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GeneratorNeZeroOfHeight
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ProdZpowEqZpowSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ScaleMultiHomogeneous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisBlock0
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.DecompBlock0
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Kernel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

noncomputable def chiImg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) :
    MvPolynomial (Fin (D + 1) × Fin N) Ω :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀
    (-∑ k, X (p.1, k) * C (x k)) (fun k => X (p.1, k)) p.2

noncomputable def chiP (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    MvPolynomial (TVar D N) K →ₐ[K] MvPolynomial (Fin (D + 1) × Fin N) Ω :=
  aeval (chiImg j₀ x)

noncomputable def kerP (j₀ : Fin (N + 1)) (x : Fin N → Ω) : Ideal (MvPolynomial (TVar D N) K) :=
  RingHom.ker (chiP (K := K) (D := D) j₀ x).toRingHom

noncomputable def psiS : MvPolynomial (Fin (D + 1) × Fin N) Ω →+* OmS Ω D N :=
  (algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)).comp
    (rename (R := Ω) (Sum.inr : Fin (D + 1) × Fin N → SVar D N)).toRingHom

theorem ker_eval_isPrime (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    (kerP (K := K) (D := D) j₀ x).IsPrime := by
  unfold kerP
  exact RingHom.ker_isPrime _

theorem psiS_chiImg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (v : TVar D N)
    (hv : ¬ (v.1 = 0 ∧ v.2 = j₀)) :
    psiS (chiImg j₀ x v) = sImg (Ω := Ω) j₀ x v := by
  obtain ⟨i, j⟩ := v
  by_cases hj : j = j₀
  · rw [hj] at hv ⊢
    have hi : i ≠ 0 := fun h => hv ⟨h, rfl⟩
    have h1 : chiImg j₀ x (i, j₀) = -∑ k, X (i, k) * C (x k) :=
      Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _
    have h2 : sImg (Ω := Ω) j₀ x (i, j₀) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr (i, k)) * C (x k)) := by
      unfold sImg
      congr 1
      exact (Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _).trans
        (if_neg hi)
    rw [h1, h2]
    simp [psiS, map_neg, map_sum, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]
  · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    rw [← hk]
    have h1 : chiImg j₀ x (i, j₀.succAbove k) = X (i, k) :=
      Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _ k
    have h2 : sImg (Ω := Ω) j₀ x (i, j₀.succAbove k) =
        algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
      unfold sImg
      congr 1
      exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k
    rw [h1, h2]
    simp [psiS, MvPolynomial.rename_X]

theorem psiS_chiImg_base (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    psiS (chiImg j₀ x ((0 : Fin (D + 1)), j₀)) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
        (-∑ k, X (Sum.inr ((0 : Fin (D + 1)), k)) * C (x k)) := by
  have h1 : chiImg j₀ x ((0 : Fin (D + 1)), j₀) = -∑ k, X ((0 : Fin (D + 1)), k) * C (x k) :=
    Fin.insertNth_apply_same (α := fun _ => MvPolynomial (Fin (D + 1) × Fin N) Ω) j₀ _ _
  rw [h1]
  simp [psiS, map_neg, map_sum, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C]

theorem sImg_base (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    sImg (Ω := Ω) j₀ x ((0 : Fin (D + 1)), j₀) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inl ())) := by
  unfold sImg
  congr 1
  first
  | exact (Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _).trans (if_pos rfl)
  | simp [Fin.succAboveCases]

theorem sImg_succAbove (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg (Ω := Ω) j₀ x (i, j₀.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k

theorem ker_eval_ne_bot (hΩ : Algebra.trdeg K Ω = D) (j₀ : Fin (N + 1)) (x : Fin N → Ω) :
    kerP (K := K) (D := D) j₀ x ≠ ⊥ := by
  intro hbot
  have hinj : Function.Injective (chiP (K := K) (D := D) j₀ x) :=
    (RingHom.injective_iff_ker_eq_bot (chiP (K := K) (D := D) j₀ x).toRingHom).mpr hbot
  have hphi : MvPolynomial.aeval (fun i : TVar D N => chiP (K := K) (D := D) j₀ x (MvPolynomial.X i)) =
      chiP (K := K) (D := D) j₀ x := by
    first
    | (ext i; simp)
    | exact (MvPolynomial.aeval_unique _).symm
  have hind : AlgebraicIndependent K
      (fun i : TVar D N => chiP (K := K) (D := D) j₀ x (MvPolynomial.X i)) := by
    rw [algebraicIndependent_iff_injective_aeval, hphi]
    exact hinj
  have h1 := hind.cardinalMk_le_trdeg
  have h2 : Algebra.trdeg K Ω + Algebra.trdeg Ω (MvPolynomial (Fin (D + 1) × Fin N) Ω) =
      Algebra.trdeg K (MvPolynomial (Fin (D + 1) × Fin N) Ω) := trdeg_add_eq K Ω
  rw [← h2, MvPolynomial.trdeg_of_isDomain, hΩ, Cardinal.mk_fintype, Cardinal.mk_fintype,
    Cardinal.lift_natCast] at h1
  have h3 : Fintype.card (TVar D N) ≤ D + Fintype.card (Fin (D + 1) × Fin N) := by exact_mod_cast h1
  simp only [TVar, Fintype.card_prod, Fintype.card_fin] at h3
  have h4 : (D + 1) * (N + 1) = (D + 1) * N + (D + 1) := by ring
  linarith

end Kernel

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem sH_X (c : ι) (v : TVar d.D d.N) : d.sH c (X v) = sImg (Ω := Ω c) (d.jc c) (d.x c) v := by
  unfold Data.sH sHom
  exact MvPolynomial.aeval_X _ _

theorem w0rat_eq_base (hd : d.AxH 𝒜) (c : ι) :
    d.rationalBaseRow c = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (X (Sum.inl ()) + ∑ k, X (Sum.inr ((0 : Fin (d.D + 1)), k)) * C (d.x c k)) := by
  have hb := hd.w_base c
  have key : ∀ (a b : Ω c) (g : A c), g ≠ 0 → a • g = b • g → a = b := by
    intro a b g hg hab
    by_contra hne
    apply hg
    have h1 : (a - b) • g = 0 := by rw [sub_smul, hab, sub_self]
    have h2 : (a - b)⁻¹ • ((a - b) • g) = g := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
    rw [← h2, h1, smul_zero]
  have hr1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := by
    have hex : ∃ a : Ω c, d.w (d.jc c) c = a • d.w (d.jc c) c := ⟨1, (one_smul _ _).symm⟩
    unfold ratio
    rw [dif_pos hex]
    exact (key _ _ _ hb ((one_smul _ _).trans hex.choose_spec)).symm
  unfold Data.rationalBaseRow
  rw [Fin.sum_univ_succAbove _ (d.jc c), hr1, map_one, mul_one]
  simp only [sH_X, sImg_succAbove, sImg_base, map_add, map_sum, map_mul]
  congr 1

theorem ker_eval_le_of_place (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)}
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) ≤ p := by
  obtain ⟨_, hw2⟩ := hw
  intro F hF
  have hF0 : chiP (K := K) (D := d.D) (d.jc c) (d.x c) F = 0 := RingHom.mem_ker.mp hF
  have hsH : ∀ v, 0 ≤ w (sImg (Ω := Ω c) (d.jc c) (d.x c) v) := fun v => by
    rw [← d.sH_X c v]
    exact (hw2 (MvPolynomial.X v)).1
  have hv : ∀ v : TVar d.D d.N, 0 ≤ w (psiS (chiImg (d.jc c) (d.x c) v)) ∧ 0 < w (sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiImg (d.jc c) (d.x c) v)) := by
    intro v
    by_cases hv0 : v.1 = 0 ∧ v.2 = d.jc c
    · obtain ⟨v1, v2⟩ := v
      obtain ⟨h1, h2⟩ := hv0
      have h1' : v1 = 0 := h1
      have h2' : v2 = d.jc c := h2
      subst h1'
      subst h2'
      have hdiff : sImg (Ω := Ω c) (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c) - psiS (chiImg (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c)) =
          d.rationalBaseRow c := by
        rw [sImg_base, psiS_chiImg_base, d.w0rat_eq_base hd c, ← map_sub]
        congr 1
        ring
      rw [hdiff]
      refine ⟨?_, hy⟩
      have e : psiS (chiImg (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c)) =
          sImg (Ω := Ω c) (d.jc c) (d.x c) ((0 : Fin (d.D + 1)), d.jc c) - d.rationalBaseRow c := by
        rw [← hdiff]
        ring
      rw [e]
      exact le_trans (le_min (hsH _) hy.le) (AddValuation.map_sub _ _ _)
    · rw [psiS_chiImg (d.jc c) (d.x c) v hv0, sub_self, AddValuation.map_zero]
      exact ⟨hsH v, by simp⟩
  have hC : ∀ k : K, d.sH c (MvPolynomial.C k) = psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.C k)) := by
    intro k
    have e1 : chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.C k) =
        algebraMap K (MvPolynomial (Fin (d.D + 1) × Fin d.N) (Ω c)) k := MvPolynomial.aeval_C _ _
    have e2 : d.sH c (MvPolynomial.C k) = algebraMap K (OmS (Ω c) d.D d.N) k :=
      MvPolynomial.aeval_C _ _
    rw [e1, e2]
    unfold psiS
    rw [RingHom.comp_apply]
    first
    | (rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
       exact IsScalarTower.algebraMap_apply K _ _ k)
    | (simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
       exact IsScalarTower.algebraMap_apply K _ _ k)
    | (simp [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)])
  have key : ∀ G : KTp K d.D d.N, 0 ≤ w (psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) G)) ∧ 0 < w (d.sH c G - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) G)) := by
    intro G
    induction G using MvPolynomial.induction_on
    · rename_i k
      rw [← hC k, sub_self, AddValuation.map_zero]
      exact ⟨(hw2 _).1, by simp⟩
    · rename_i p q hp hq
      simp only [map_add]
      refine ⟨le_trans (le_min hp.1 hq.1) (AddValuation.map_add _ _ _), ?_⟩
      have e : d.sH c p + d.sH c q - (psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p) + psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) q)) =
          (d.sH c p - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p)) + (d.sH c q - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) q)) := by ring
      rw [e]
      exact lt_of_lt_of_le (lt_min hp.2 hq.2) (AddValuation.map_add _ _ _)
    · rename_i p v hp
      have hX : chiP (K := K) (D := d.D) (d.jc c) (d.x c) (MvPolynomial.X v) = chiImg (d.jc c) (d.x c) v := MvPolynomial.aeval_X _ _
      rw [map_mul (chiP (K := K) (D := d.D) (d.jc c) (d.x c)) p (MvPolynomial.X v), hX,
        map_mul (psiS (Ω := Ω c) (D := d.D) (N := d.N)), map_mul (d.sH c) p (MvPolynomial.X v),
        d.sH_X c v]
      refine ⟨by rw [AddValuation.map_mul]; exact add_nonneg hp.1 (hv v).1, ?_⟩
      have e : d.sH c p * sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p) * psiS (chiImg (d.jc c) (d.x c) v) =
          d.sH c p * (sImg (Ω := Ω c) (d.jc c) (d.x c) v - psiS (chiImg (d.jc c) (d.x c) v)) + (d.sH c p - psiS (chiP (K := K) (D := d.D) (d.jc c) (d.x c) p)) * psiS (chiImg (d.jc c) (d.x c) v) := by ring
      rw [e]
      refine lt_of_lt_of_le (lt_min ?_ ?_) (AddValuation.map_add _ _ _)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le (hv v).2 (le_add_of_nonneg_left (hw2 p).1)
      · rw [AddValuation.map_mul]
        exact lt_of_lt_of_le hp.2 (le_add_of_nonneg_right (hv v).1)
  apply (hw2 F).2.mp
  have h := (key F).2
  rw [hF0, map_zero, sub_zero] at h
  exact h

theorem ker_eval_eq_of_place (hd : d.AxH 𝒜) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.OverP c p)
    (htriv : ∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) (hy : 0 < w (d.rationalBaseRow c)) :
    kerP (K := K) (D := d.D) (d.jc c) (d.x c) = p := by
  have hle := d.ker_eval_le_of_place hd c hw htriv hy
  have hprime := ker_eval_isPrime (K := K) (D := d.D) (d.jc c) (d.x c)
  have hne := ker_eval_ne_bot (K := K) (hd.trdeg c) (d.jc c) (d.x c)
  obtain ⟨hpp, hph⟩ := hp
  by_contra hneq
  have hlt := lt_of_le_of_ne hle hneq
  have h1 : p.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hph]; simp
  have h2 := (Ideal.height_le_iff.mp h1) _ hprime hlt
  have h3 : ¬ (kerP (K := K) (D := d.D) (d.jc c) (d.x c)).height ≤ ((0 : ℕ) : ℕ∞) := by
    intro h0
    have h4 := (Ideal.height_le_iff.mp h0) ⊥ Ideal.bot_prime (bot_lt_iff_ne_bot.mpr hne)
    simp at h4
  apply h3
  have h5 : (kerP (K := K) (D := d.D) (d.jc c) (d.x c)).height = 0 :=
    ENat.lt_one_iff_eq_zero.mp (by simpa using h2)
  rw [h5]
  simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open MvPolynomial

section Swap

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

def swapT : TVar D N ≃ TVar D N := Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)

def swapS : (Fin (D + 1) × Fin N) ≃ (Fin (D + 1) × Fin N) :=
  Equiv.prodCongr (Equiv.swap 0 1) (Equiv.refl _)

theorem chiP_rename_swap (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K) :
    chiP (K := K) j₀ x (rename swapT g) = rename swapS (chiP (K := K) j₀ x g) := by
  have key : ∀ p : TVar D N, chiImg j₀ x (swapT p) = rename swapS (chiImg j₀ x p) := by
    rintro ⟨b, j⟩
    rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
    · simp [chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_same, map_sum, map_neg]
    · simp [chiImg, swapT, swapS, Fin.succAbove_cases_eq_insertNth, Fin.insertNth_apply_succAbove]
  induction g using MvPolynomial.induction_on with
  | C a => simp [chiP]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    simp only [chiP, aeval_X, key]

theorem rename_swap_mem_ker_eval (j₀ : Fin (N + 1)) (x : Fin N → Ω) (g : MvPolynomial (TVar D N) K)
    (hg : g ∈ kerP (K := K) (D := D) j₀ x) : rename swapT g ∈ kerP (K := K) (D := D) j₀ x := by
  rw [kerP, RingHom.mem_ker] at hg ⊢
  have hg' : chiP (K := K) j₀ x g = 0 := hg
  show chiP (K := K) j₀ x (rename swapT g) = 0
  rw [chiP_rename_swap, hg', map_zero]

end Swap

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem fZ_factor_height_one_primes (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ κ : K, κ ≠ 0 ∧ ∃ T : Finset (Ideal (KTp K d.D d.N)), ∃ e : Ideal (KTp K d.D d.N) → ℕ,
      (∀ p ∈ T, p ∈ d.HtOne) ∧ F = C κ * ∏ p ∈ T, d.gen p ^ e p ∧
      ∀ p ∈ T, e p ≠ 0 → ∃ w ∈ d.OverP c p, (∀ a : Ω c, a ≠ 0 → d.Wres c w a = 0) ∧
        0 < w (d.rationalBaseRow c) := by
  classical
  have hy : d.rationalBaseRow c ≠ 0 := d.lineRatio_ne_zero hd c
  obtain ⟨hfin, hall⟩ := d.norm_by_places hd h c
  obtain ⟨hSy, κ, hκ, hN⟩ := hall _ hy
  set T := hSy.toFinset with hT
  set Gm : Ideal (KTp K d.D d.N) → KTf K d.D d.N :=
    fun p => algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hGm
  set a : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) with ha
  set b : Ideal (KTp K d.D d.N) → ℤ := fun p => d.nPMM h c (d.w (d.jc c) c) p with hb
  have hmemT : ∀ p, p ∈ T ↔ p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w (d.rationalBaseRow c) ≠ 0 := fun p =>
    Set.Finite.mem_toFinset hSy
  have hGne : ∀ p ∈ d.HtOne, Gm p ≠ 0 := fun p hp => by
    simp only [hGm]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N))).mpr
      (d.generator_ne_zero_of_height p hp)

  have hoff : ∀ p ∈ d.HtOne, p ∉ T → ∀ w ∈ d.OverP c p, w (d.rationalBaseRow c) = 0 := by
    intro p hp hpT w hw
    by_contra hne
    exact hpT ((hmemT p).mpr ⟨hp, w, hw, hne⟩)
  have ha0 : ∀ p ∈ d.HtOne, p ∉ T → a p = 0 := by
    intro p hp hpT
    simp only [ha]
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)]
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [hoff p hp hpT w ((Set.Finite.mem_toFinset _).mp hw)]
    simp
  have hb0 : ∀ p ∈ d.HtOne, p ∉ T → b p = 0 := by
    intro p hp hpT
    simp only [hb, Data.nPMM]
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
    refine Finset.sum_eq_zero fun w hw => ?_
    have hw' := (Set.Finite.mem_toFinset _).mp hw
    have := d.good_valuation_balance hd h c p hp w hw'
    rw [hoff p hp hpT w hw'.1] at this
    simp at this
    rw [this, mul_zero]
  have hab : ∀ p ∈ d.HtOne, 0 ≤ a p + b p := by
    intro p hp
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    have e1 : a p = ∑ w ∈ (hfin p hp).toFinset,
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)
    have e2 : b p = ∑ w ∈ (hfin p hp).toFinset,
        if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0 := by
      rw [← Finset.sum_filter]
      simp only [hb, Data.nPMM]
      rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
      congr 1
      ext w
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun w hw => ?_
    have hwO := (Set.Finite.mem_toFinset _).mp hw
    by_cases hg : w ∈ d.GoodP c p
    · rw [if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero]
    · rw [if_neg hg, add_zero]
      refine mul_nonneg (by positivity) (untopD_nonneg ?_)
      refine d.lineRatio_val_nonneg c p w hwO fun a0 ha0' => ?_
      by_contra hne
      exact hg ⟨hwO, a0, ha0', hne⟩
  have hTsub : (T : Set (Ideal (KTp K d.D d.N))) ⊆ d.HtOne := fun p hp => ((hmemT p).mp hp).1
  have e1 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ a p) = ∏ p ∈ T, Gm p ^ a p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTsub
    rintro p ⟨hp, hne⟩
    by_contra hpT
    exact hne (by simp only [ha0 p hp hpT, zpow_zero])
  have e2 : (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), Gm p ^ b p) = ∏ p ∈ T, Gm p ^ b p := by
    refine finprod_mem_eq_prod_of_subset _ ?_ hTsub
    rintro p ⟨hp, hne⟩
    by_contra hpT
    exact hne (by simp only [hb0 p hp hpT, zpow_zero])
  have hfZ : d.fZ h c = algebraMap K (KTf K d.D d.N) κ * ∏ p ∈ T, Gm p ^ (a p + b p) := by
    have hN' := hN
    unfold Data.fZ
    rw [hN', e1, e2, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p hp => (zpow_add₀ (hGne p (hTsub hp)) _ _).symm
  refine ⟨κ, hκ, T, fun p => (a p + b p).toNat, fun p hp => hTsub hp, ?_, ?_⟩
  · apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    rw [hF, hfZ, map_mul, map_prod, ← d.algebraMap_K_KTf]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (hab p (hTsub hp))]
  · intro p hpT he
    have hp := hTsub hpT
    have hne : a p + b p ≠ 0 := fun h0 => he (by simp only [h0, Int.toNat_zero])
    have hGf : (d.GoodP c p).Finite := (hfin p hp).subset fun w hw => hw.1
    have e1 : a p = ∑ w ∈ (hfin p hp).toFinset,
        (d.fze h c w : ℤ) * WithTop.untopD 0 (w (d.rationalBaseRow c)) :=
      finsum_mem_eq_finite_toFinset_sum _ (hfin p hp)
    have e2 : b p = ∑ w ∈ (hfin p hp).toFinset,
        if w ∈ d.GoodP c p then (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c) else 0 := by
      rw [← Finset.sum_filter]
      simp only [hb, Data.nPMM]
      rw [finsum_mem_eq_finite_toFinset_sum _ hGf]
      congr 1
      ext w
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun hw => ⟨hw.1, hw⟩, fun hw => hw.2⟩
    rw [e1, e2, ← Finset.sum_add_distrib] at hne
    obtain ⟨w, hwF, hw0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hwO := (Set.Finite.mem_toFinset _).mp hwF
    by_cases hg : w ∈ d.GoodP c p
    · rw [if_pos hg, ← mul_add, d.good_valuation_balance hd h c p hp w hg, mul_zero] at hw0
      exact absurd rfl hw0
    · rw [if_neg hg, add_zero] at hw0
      have htriv : ∀ a0 : Ω c, a0 ≠ 0 → d.Wres c w a0 = 0 := fun a0 ha0 => by
        by_contra hne'
        exact hg ⟨hwO, a0, ha0, hne'⟩
      have hnn := d.lineRatio_val_nonneg c p w hwO htriv
      have hu : WithTop.untopD 0 (w (d.rationalBaseRow c)) ≠ 0 := right_ne_zero_of_mul hw0
      exact ⟨w, hwO, htriv, lt_of_le_of_ne hnn fun h0 => hu (by rw [← h0]; rfl)⟩

theorem rename_swap_F (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ∃ ρ : K, rename swapT F = C ρ * F := by
  classical
  obtain ⟨κ, hκ, T, e, hT, hFeq, hplace⟩ := d.fZ_factor_height_one_primes hd h c F hF
  set P := kerP (K := K) (D := d.D) (d.jc c) (d.x c) with hP
  have hker : ∀ p ∈ T, e p ≠ 0 → p = P := by
    intro p hp hep
    obtain ⟨w, hw, htriv, hy⟩ := hplace p hp hep
    exact (d.ker_eval_eq_of_place hd c (hT p hp) hw htriv hy).symm
  by_cases hex : ∃ p ∈ T, e p ≠ 0
  · obtain ⟨p0, hp0, hep0⟩ := hex
    have hPone : P ∈ d.HtOne := by
      rw [← hker p0 hp0 hep0]
      exact hT p0 hp0
    have hg0 : d.gen P ≠ 0 := d.generator_ne_zero_of_height P hPone
    have hprin : P.IsPrincipal := by
      by_contra hnp
      apply hg0
      unfold Data.gen
      rw [dif_neg hnp]
    have hgspan : Ideal.span {d.gen P} = P := by
      unfold Data.gen
      rw [dif_pos hprin]
      exact Ideal.span_singleton_generator P
    have hFg : F = C κ * d.gen P ^ (∑ p ∈ T, e p) := by
      rw [hFeq, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      refine Finset.prod_congr rfl fun p hp => ?_
      by_cases hep : e p = 0
      · rw [hep, pow_zero, pow_zero]
      · rw [hker p hp hep]
    have hren : ∃ r : K, rename swapT (d.gen P) = C r * d.gen P := by
      have hmem0 : d.gen P ∈ P := by
        have h1 := Ideal.mem_span_singleton_self (d.gen P)
        rwa [hgspan] at h1
      have hmem : rename swapT (d.gen P) ∈ P := rename_swap_mem_ker_eval (K := K) (D := d.D) (d.jc c) (d.x c) _ hmem0
      have hmem' : rename swapT (d.gen P) ∈ Ideal.span {d.gen P} := by
        rw [hgspan]
        exact hmem
      rw [Ideal.mem_span_singleton] at hmem'
      obtain ⟨q, hq⟩ := hmem'
      have hq0 : q ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hq
        apply hg0
        apply MvPolynomial.rename_injective _ (swapT (D := d.D) (N := d.N)).injective
        rw [map_zero]
        exact hq
      have hdeg := MvPolynomial.totalDegree_rename_le (swapT (D := d.D) (N := d.N)) (d.gen P)
      rw [hq, MvPolynomial.totalDegree_mul_of_isDomain hg0 hq0] at hdeg
      have hq' : q.totalDegree = 0 := by omega
      rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq'
      obtain ⟨a, ha⟩ : ∃ a : K, q = C a := ⟨_, hq'⟩
      exact ⟨a, by rw [hq, ha, mul_comm]⟩
    obtain ⟨r, hr⟩ := hren
    refine ⟨r ^ (∑ p ∈ T, e p), ?_⟩
    rw [hFg, map_mul, MvPolynomial.rename_C, map_pow, hr, mul_pow, ← map_pow]
    ring
  · push_neg at hex
    have hF1 : F = C κ := by
      rw [hFeq]
      have h1 : ∏ p ∈ T, d.gen p ^ e p = 1 := Finset.prod_eq_one fun p hp => by rw [hex p hp, pow_zero]
      rw [h1, mul_one]
    exact ⟨1, by rw [hF1, MvPolynomial.rename_C, map_one, one_mul]⟩

theorem fZ_multiHomogeneous_degree_sum (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c := by
  classical
  obtain ⟨F', hF', hF'0⟩ := d.componentForm_poly hd h c
  have hFF : F = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (hF.trans hF'.symm)
  have hF0 : F ≠ 0 := hFF ▸ hF'0
  obtain ⟨hdeg0, hdegb⟩ := d.F_degrees hd h c F hF
  obtain ⟨ρ, hρ⟩ := d.rename_swap_F hd h c F hF
  have h10 : (1 : Fin (d.D + 1)) ≠ 0 := by
    have hD := hd.D_ge
    intro h1
    have h2 := congrArg (fun i : Fin (d.D + 1) => (i : ℕ)) h1
    first
    | (simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < d.D + 1 by omega)] at h2; omega)
    | (simp at h2; omega)
    | (simp [Fin.val_one'] at h2; omega)
  obtain ⟨s, hs⟩ : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hF0
  have ht : s.mapDomain swapT ∈ F.support := by
    have h1 : (rename swapT F).coeff (s.mapDomain swapT) = F.coeff s :=
      MvPolynomial.coeff_rename_mapDomain _ (swapT (D := d.D) (N := d.N)).injective F s
    rw [hρ, MvPolynomial.coeff_C_mul] at h1
    rw [MvPolynomial.mem_support_iff] at hs ⊢
    intro h0
    rw [h0, mul_zero] at h1
    exact hs h1.symm
  have key : (d.aMM h c).toNat = d.delc c := by
    rw [← hdegb 1 h10 s hs, ← hdeg0 _ ht]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsw : (swapT (D := d.D) (N := d.N)) (1, j) = (0, j) := by
      simp [swapT, Equiv.swap_apply_right]
    rw [← hsw, Finsupp.mapDomain_apply (swapT (D := d.D) (N := d.N)).injective]
  have hA : d.aMM h c = d.delc c := by
    have h1 := d.aMM_nonneg hd h c
    omega
  refine ⟨?_, hA⟩
  intro s' hs' b
  by_cases hb : b = 0
  · subst hb
    exact hdeg0 s' hs'
  · rw [hdegb b hb s' hs', key]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem DegreeSumIdentity (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c := by
  exact d.fZ_multiHomogeneous_degree_sum hd h c F hF

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

theorem hx4v2_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {g : V}
    (hg : g ≠ 0) (s : Ω) : ratio (Ω := Ω) (s • g) g = s := by
  unfold ratio
  have hex : ∃ a : Ω, s • g = a • g := ⟨s, rfl⟩
  rw [dif_pos hex]
  exact (smul_left_injective Ω hg hex.choose_spec).symm

theorem hx4v2_eq_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (W : Submodule Ω V) (hW : Module.finrank Ω W = 1) {f g : V} (hf : f ∈ W) (hgW : g ∈ W)
    (hg : g ≠ 0) : f = ratio (Ω := Ω) f g • g := by
  have hg' : (⟨g, hgW⟩ : W) ≠ 0 := fun e => hg (congrArg Subtype.val e)
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hgW⟩ : W) hg').mp hW ⟨f, hf⟩
  have hex : ∃ a : Ω, f = a • g := ⟨a, (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hx4v2_ratio_wx (hd : d.AxH 𝒜) (c : ι) (x : Fin (d.N + 1) → K) :
    ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c) =
      ∑ j, algebraMap K (Ω c) (x j) * ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) := by
  have := hd.tower c
  have hg := hd.w_base c
  have hrep : ∀ j, d.w j c = ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) • d.w (d.jc c) c :=
    fun j => hx4v2_eq_ratio_smul _ (hd.finrank_one c d.wL) (hd.w_mem j c) (hd.w_mem (d.jc c) c) hg
  have hsum : d.wx x c = (∑ j, algebraMap K (Ω c) (x j) *
      ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) • d.w (d.jc c) c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [hrep j]
    rw [mul_smul, algebraMap_smul]
  rw [hsum, hx4v2_ratio_smul hg]

theorem norm_generic_ratio_spec (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ P Q : KTp K d.D d.N, Q ≠ 0 ∧ (∀ x, d.sub0 x Q = Q) ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) P =
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)) ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 →
        (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x P) =
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
              Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
                (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)))) := by
  let _ : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨n, b, Q0, M, hQ0, hQ0s, hMs, hM⟩ := d.basis_block0 hd h c
  let r : Fin (d.N + 1) → OmS (Ω c) d.D d.N := fun j =>
    algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
  let ι0 : KTp K d.D d.N →+* KTf K d.D d.N := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
  have hQ0' : ι0 Q0 ≠ 0 := fun e =>
    hQ0 (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (by rw [e, map_zero]))
  have key : ∀ a : Fin (d.N + 1) → KTp K d.D d.N,
      Algebra.norm (KTf K d.D d.N) (∑ j, ι0 (a j) • r j) = ι0 (∑ j, a j • M j).det / ι0 Q0 ^ n := by
    intro a
    rw [Algebra.norm_eq_matrix_det b, map_sum]
    simp_rw [map_smul]
    have hmat : (∑ j, ι0 (a j) • Algebra.leftMulMatrix b (r j)) =
        (ι0 Q0)⁻¹ • (∑ j, a j • M j).map ι0 := by
      ext i i'
      rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.sum_apply, map_sum,
        Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM j, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
        smul_eq_mul, map_mul]
      ring
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
    have hdet : ((∑ j, a j • M j).map ι0).det = ι0 (∑ j, a j • M j).det :=
      (RingHom.map_det ι0 _).symm
    rw [hdet, inv_pow, div_eq_mul_inv, mul_comm]
  have hw0 : d.rationalBaseRow c = ∑ j, ι0 (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • r j := by
    simp only [Data.rationalBaseRow]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, r]
  refine ⟨(∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det, Q0 ^ n, pow_ne_zero _ hQ0,
    fun x => by rw [map_pow, hQ0s], ?_, ?_⟩
  · show ι0 _ = ι0 (Q0 ^ n) * Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c)
    rw [hw0, key, map_pow]
    field_simp
  · intro x _
    have hs : d.sub0 x (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j).det =
        (∑ j, (MvPolynomial.C (x j) : KTp K d.D d.N) • M j).det := by
      have hmd := RingHom.map_det (d.sub0 x : KTp K d.D d.N →+* KTp K d.D d.N)
        (∑ j, (MvPolynomial.X ((0 : Fin (d.D + 1)), j) : KTp K d.D d.N) • M j)
      rw [RingHom.coe_coe] at hmd
      rw [hmd]
      congr 1
      ext i i'
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, map_sum, map_mul, RingHom.coe_coe, hMs]
      simp
    have hr : algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c)) =
        ∑ j, ι0 (MvPolynomial.C (x j) : KTp K d.D d.N) • r j := by
      rw [d.hx4v2_ratio_wx hd c x, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      congr 1
      simp only [Data.KTtoS, ι0, IsFractionRing.lift_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      exact (IsScalarTower.algebraMap_apply K (Ω c) (OmS (Ω c) d.D d.N) (x j)).symm
    show ι0 _ = ι0 (Q0 ^ n) * _
    rw [hs, hr, key, map_pow]
    field_simp

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem substRowZero_fix_of_degree_zero (x : Fin (d.N + 1) → K) (q : KTp K d.D d.N)
    (hq : ∀ s ∈ q.support, ∑ j, s (0, j) = 0) : d.sub0 x q = q := by
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  conv_rhs => rw [q.as_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h0 : ∀ j, s (0, j) = 0 := fun j =>
    (Finset.sum_eq_zero_iff.mp (hq s hs)) j (Finset.mem_univ _)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v hv => ?_
  have hv0 : v.1 ≠ 0 := by
    intro h1
    apply Finsupp.mem_support_iff.mp hv
    have e : ((0 : Fin (d.D + 1)), v.2) = v := Prod.ext h1.symm rfl
    rw [← e]
    exact h0 v.2
  simp [hv0]

theorem pi_free (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (f : A c) :
    ∃ Pp Pm : KTp K d.D d.N, Pm ≠ 0 ∧ (∀ x, d.sub0 x Pp = Pp) ∧ (∀ x, d.sub0 x Pm = Pm) ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pp =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c f p := by
  classical
  have hfix : ∀ p ∈ d.HtOne, d.nPMM h c f p ≠ 0 → ∀ x, d.sub0 x (d.gen p) = d.gen p := by
    intro p hp hn x
    have hw : ∃ w, w ∈ d.GoodP c p := by
      by_contra hno
      push_neg at hno
      exact hn (by simp [Data.nPMM, hno])
    have hm := d.GeneratorMultiHomogeneous hd h c p hp hw
    refine d.substRowZero_fix_of_degree_zero x (d.gen p) fun s hs => ?_
    simpa using hm s hs 0
  rw [finprod_mem_def, finprod_def]
  split_ifs with hfin
  · set T := hfin.toFinset with hT
    have hTmem : ∀ p ∈ T, p ∈ d.HtOne ∧ d.nPMM h c f p ≠ 0 := by
      intro p hpT
      have hpT' : p ∈ Function.mulSupport (d.HtOne.mulIndicator fun p =>
          (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) (d.gen p) ^ d.nPMM h c f p) :=
        (Set.Finite.mem_toFinset (hs := hfin)).mp hpT
      rw [Function.mem_mulSupport] at hpT'
      by_cases hp : p ∈ d.HtOne
      · refine ⟨hp, fun h0 => hpT' ?_⟩
        simp [Set.mulIndicator_of_mem hp, h0]
      · simp [hp] at hpT'
    refine ⟨∏ p ∈ T, d.gen p ^ (d.nPMM h c f p).toNat,
      ∏ p ∈ T, d.gen p ^ (-d.nPMM h c f p).toNat, ?_, ?_, ?_, ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (d.generator_ne_zero_of_height p (hTmem p hp).1)
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · intro x
      rw [map_prod]
      exact Finset.prod_congr rfl fun p hp => by
        rw [map_pow, hfix p (hTmem p hp).1 (hTmem p hp).2 x]
    · rw [map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.mulIndicator_of_mem (hTmem p hp).1]
      have ha : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
        rw [Ne, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)),
          (IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)).eq_iff]
        exact d.generator_ne_zero_of_height p (hTmem p hp).1
      rw [map_pow, map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ ha]
      congr 1
      omega
  · exact ⟨1, 1, one_ne_zero, fun x => map_one _, fun x => map_one _, by simp⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem x4v4_ratio_spec {Ω' V : Type*} [Field Ω'] [AddCommGroup V] [Module Ω' V] {f g : V}
    (hg : g ≠ 0) {a : Ω'} (hf : f = a • g) : ratio (Ω := Ω') f g = a := by
  have hex : ∃ b : Ω', f = b • g := ⟨a, hf⟩
  unfold ratio
  rw [dif_pos hex]
  have h2 : hex.choose • g = a • g := hex.choose_spec.symm.trans hf
  exact smul_left_injective Ω' hg h2

theorem x4v4_eq_smul (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) :
    f = ratio (Ω := Ω c) f (d.w (d.jc c) c) • d.w (d.jc c) c := by
  have hw0 : d.w (d.jc c) c ≠ 0 := hd.w_base c
  have hv : (⟨d.w (d.jc c) c, hd.w_mem _ c⟩ : 𝒜 c d.wL) ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Subtype.val h0
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).1 (hd.finrank_one c d.wL) ⟨f, hf⟩
  have hfa : f = a • d.w (d.jc c) c := by
    have h1 := congrArg Subtype.val ha
    simpa using h1.symm
  rw [x4v4_ratio_spec hw0 hfa]
  exact hfa

theorem x4v4_ratio_ne (hd : d.AxH 𝒜) (c : ι) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    ratio (Ω := Ω c) f (d.w (d.jc c) c) ≠ 0 := by
  intro h0
  apply hf0
  rw [x4v4_eq_smul d hd c hf, h0, zero_smul]

theorem x4v4_wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  have e : d.wx x c = ∑ j, x j • d.w j c := by
    simp only [Data.wx, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem x4v4_gen_ne {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ?_
  obtain ⟨hprime, hh⟩ := hp
  have hpr := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
  unfold gen
  rw [dif_pos hpr]
  intro h0
  exact p.ne_bot_of_height_eq_one hh ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero p).mpr h0)

theorem x4v4_ordMM (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) {f : A c}
    (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.ordMM c (d.Wres c w) f = WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c))) +
      d.ordMM c (d.Wres c w) (d.w (d.jc c) c) := by
  have hA := d.good_adm hd h c hp hw
  have e : ((d.ord c (d.Wres c w) d.wL f : ℤ) : WithTop ℤ) =
      d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) +
        (d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : WithTop ℤ) := by
    conv_lhs => rw [d.x4v4_eq_smul hd c hf]
    exact hd.ord_smul c _ hA _ (hd.w_mem _ _) (hd.w_base c) (d.x4v4_ratio_ne hd c hf hf0)
  have hfin : d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) =
      ((d.ord c (d.Wres c w) d.wL f - d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) : ℤ) : WithTop ℤ) := by
    revert e
    generalize d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)) = t
    intro e
    induction t using WithTop.recTopCoe with
    | top => simp at e
    | coe t =>
      have e' : d.ord c (d.Wres c w) d.wL f = t + d.ord c (d.Wres c w) d.wL (d.w (d.jc c) c) := by
        exact_mod_cast e
      rw [e']
      congr 1
      ring
  unfold ordMM
  rw [hfin, WithTop.untopD_coe]
  ring

theorem x4v4_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) {f : A c} (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    d.nPMM h c f p =
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w (ratio (Ω := Ω c) f (d.w (d.jc c) c)))) +
      d.nPMM h c (d.w (d.jc c) c) p := by
  have hfin := d.goodP_finite hd h c hp
  unfold nPMM
  rw [← finsum_mem_add_distrib hfin]
  refine finsum_mem_congr rfl fun w hw => ?_
  rw [d.x4v4_ordMM hd h c hp hw hf hf0]
  ring

theorem norm_ratio_pi (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (x : Fin (d.N + 1) → K)
    (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra;
        Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N)
            (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.w (d.jc c) c) p =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p) := by
  classical
  have hmem := d.x4v4_wx_mem hd x c
  have hg0 := d.x4v4_ratio_ne hd c hmem hx
  obtain ⟨κ, hκ, hN⟩ := d.norm_factorization_clause hd h c _ hg0
  refine ⟨κ, hκ, ?_⟩
  rw [hN, mul_assoc]
  congr 1
  set na : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0
        (d.Wres c w (ratio (Ω := Ω c) (d.wx x c) (d.w (d.jc c) c))) with hna
  set G : Ideal (KTp K d.D d.N) → KTf K d.D d.N := fun p =>
    algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) with hG
  have hsplit : ∀ p ∈ d.HtOne, d.nPMM h c (d.wx x c) p = na p + d.nPMM h c (d.w (d.jc c) c) p :=
    fun p hp => d.x4v4_split hd h c hp hmem hx
  have hSx := (d.good_primes_properties hd h c).2.2.2 _ hmem hx
  have hSj := (d.good_primes_properties hd h c).2.2.2 _ (hd.w_mem _ c) (hd.w_base c)
  have hfa : (d.HtOne ∩ Function.mulSupport fun p => G p ^ na p).Finite := by
    refine (hSx.union hSj).subset fun p hp => ?_
    have hn : na p ≠ 0 := by
      intro h0; apply hp.2; simp only [h0, zpow_zero]
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_not] at hc
    apply hn
    have e := hsplit p hp.1
    rw [hc.1 hp.1, hc.2 hp.1] at e
    omega
  have hfj : (d.HtOne ∩ Function.mulSupport fun p => G p ^ d.nPMM h c (d.w (d.jc c) c) p).Finite := by
    refine hSj.subset fun p hp => ⟨hp.1, ?_⟩
    intro h0; apply hp.2; simp only [h0, zpow_zero]
  show (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ na p) *
      (∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.w (d.jc c) c) p) =
    ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), G p ^ d.nPMM h c (d.wx x c) p
  rw [← finprod_mem_mul_distrib' hfa hfj]
  refine finprod_mem_congr rfl fun p hp => ?_
  rw [hsplit p hp, zpow_add₀ (d.x4v4_gen_ne hp)]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem SpecialFibreFactorization (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c)
    (x : Fin (d.N + 1) → K) (hx : d.wx x c ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
        (MvPolynomial.aeval (fun v : TVar d.D d.N =>
          if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
      algebraMap K (KTf K d.D d.N) κ *
        ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  classical
  obtain ⟨P, Q, hQ0, hQx, hPQ, hspec⟩ := d.norm_generic_ratio_spec hd h c
  obtain ⟨Pp, Pm, hPm0, hPpx, hPmx, hPi⟩ := d.pi_free hd h c (d.w (d.jc c) c)
  obtain ⟨κ, hκ, hκeq⟩ := d.norm_ratio_pi hd h c x hx
  refine ⟨κ, hκ, ?_⟩
  have hφinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hpoly : Q * F * Pm = P * Pp := by
    apply hφinj
    simp only [map_mul]
    rw [hF, hPi, hPQ]
    simp only [fZ]
    ring
  have hsub := congrArg (d.sub0 x) hpoly
  simp only [map_mul, hQx, hPmx, hPpx] at hsub
  have hφ := congrArg (algebraMap (KTp K d.D d.N) (KTf K d.D d.N)) hsub
  simp only [map_mul] at hφ
  rw [hspec x hx, hPi] at hφ
  have hQ' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hQ0
  have hPm' : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm ≠ 0 :=
    (map_ne_zero_iff _ hφinj).mpr hPm0
  rw [← hκeq]
  apply mul_left_cancel₀ (mul_ne_zero hQ' hPm')
  calc _ = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Q *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.sub0 x F) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) Pm := by ring
    _ = _ := hφ
    _ = _ := by ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end

section
namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem componentForm_properties (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    ∃ F : KTp K d.D d.N, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c ∧ F ≠ 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c ∧
      ∀ x : Fin (d.N + 1) → K, d.wx x c ≠ 0 → ∃ κ : K, κ ≠ 0 ∧
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
          (MvPolynomial.aeval (fun v : TVar d.D d.N =>
            if v.1 = 0 then MvPolynomial.C (x v.2) else MvPolynomial.X v) F) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ d.nPMM h c (d.wx x c) p := by
  obtain ⟨F, hF, hF0⟩ := d.componentForm_poly hd h c
  obtain ⟨hmh, hmm⟩ := d.DegreeSumIdentity hd h c F hF
  exact ⟨F, hF, hF0, hmh, hmm, fun x hx => d.SpecialFibreFactorization hd h c F hF x hx⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
end
