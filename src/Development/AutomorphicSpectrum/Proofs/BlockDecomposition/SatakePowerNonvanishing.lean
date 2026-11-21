import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriFactorization
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AOpRightInvariant

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.BruhatIw

section Mat

variable {L : Type} [Field L] {σ : L →+* L} {n : ℕ}

abbrev mat (g : GU σ n) : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

theorem mat_mul_apply (g h : GU σ n) (i j : Fin n) :
    mat (g * h) i j = ∑ l, mat g i l * mat h l j := by
  show ((mat g) * (mat h)) i j = _
  rw [Matrix.mul_apply]

theorem mat_one_apply (i j : Fin n) : mat (1 : GU σ n) i j = if i = j then 1 else 0 := by
  show (1 : Matrix (Fin n) (Fin n) L) i j = _
  rw [Matrix.one_apply]

theorem mat_inv_apply (g : GU σ n) (i j : Fin n) : mat g⁻¹ i j = σ (mat g j.rev i.rev) :=
  (GlobalTheory.LGrp.mem_GU_iff σ n g.1).1 g.2 i j

theorem sum_mul_inv (g : GU σ n) (i j : Fin n) :
    ∑ l, mat g i l * mat g⁻¹ l j = if i = j then 1 else 0 := by
  rw [← mat_mul_apply, mul_inv_cancel, mat_one_apply]

theorem sum_inv_mul (g : GU σ n) (i j : Fin n) :
    ∑ l, mat g⁻¹ i l * mat g l j = if i = j then 1 else 0 := by
  rw [← mat_mul_apply, inv_mul_cancel, mat_one_apply]

theorem row_form (g : GU σ n) (i j : Fin n) :
    ∑ l, mat g i l * σ (mat g j.rev l.rev) = if i = j then 1 else 0 := by
  rw [← sum_mul_inv g i j]
  exact Finset.sum_congr rfl fun l _ => by rw [mat_inv_apply]

theorem row_isotropic (g : GU σ n) {a : Fin n} (ha : a ≠ a.rev) :
    ∑ l, mat g a l * σ (mat g a l.rev) = 0 := by
  have h := row_form g a a.rev
  rwa [if_neg ha, Fin.rev_rev] at h

theorem row_ne_zero (g : GU σ n) (a : Fin n) : ∃ j, mat g a j ≠ 0 := by
  by_contra h
  push_neg at h
  have := sum_mul_inv g a a
  simp [h] at this

theorem exists_GU (T S : Matrix (Fin n) (Fin n) L) (h : T * S = 1)
    (hS : ∀ i j, S i j = σ (T j.rev i.rev)) : ∃ g : GU σ n, mat g = T :=
  ⟨⟨⟨T, S, h, mul_eq_one_comm.1 h⟩, (GlobalTheory.LGrp.mem_GU_iff σ n _).2 fun i j => hS i j⟩, rfl⟩

def trU (g : GU σ n) : GU σ n :=
  ⟨⟨(mat g).transpose, (mat g⁻¹).transpose,
    by rw [← Matrix.transpose_mul]
       show (mat (g⁻¹ * g)).transpose = 1
       rw [inv_mul_cancel]; exact Matrix.transpose_one,
    by rw [← Matrix.transpose_mul]
       show (mat (g * g⁻¹)).transpose = 1
       rw [mul_inv_cancel]; exact Matrix.transpose_one⟩,
   (GlobalTheory.LGrp.mem_GU_iff σ n _).2 fun i j => mat_inv_apply g j i⟩

theorem trU_trU (g : GU σ n) : trU (trU g) = g := by
  apply Subtype.ext; apply Units.ext; rfl

theorem trU_mul (g h : GU σ n) : trU (g * h) = trU h * trU g := by
  apply Subtype.ext; apply Units.ext
  show (mat g * mat h).transpose = (mat h).transpose * (mat g).transpose
  rw [Matrix.transpose_mul]

theorem trU_one : trU (1 : GU σ n) = 1 := by
  apply Subtype.ext; apply Units.ext
  exact Matrix.transpose_one

def eichM (σ : L →+* L) (p : Fin n) (z : Fin n → L) : Matrix (Fin n) (Fin n) L := fun i j =>
  if i = p then z j
  else if j = p.rev then (if i = p.rev then 1 else - σ (z i.rev))
  else if i = j then 1 else 0

theorem eich_dual (hσ : ∀ x, σ (σ x) = x) (p : Fin n) (z : Fin n → L) (i j : Fin n) :
    σ (eichM σ p z j.rev i.rev) =
      if j = p.rev then σ (z i.rev)
      else if i = p then (if j = p then 1 else - z j)
      else if i = j then 1 else 0 := by
  unfold eichM
  by_cases hj : j = p.rev
  · subst hj; simp
  · have h1 : ¬ j.rev = p := fun h => hj (by rw [← h, Fin.rev_rev])
    rw [if_neg h1, if_neg hj]
    by_cases hi : i = p
    · subst hi
      by_cases hj' : j = i
      · subst hj'; simp
      · have h2 : ¬ j.rev = i.rev := fun h => hj' (Fin.rev_injective h)
        simp [h2, hj', hσ]
    · have h2 : ¬ i.rev = p.rev := fun h => hi (Fin.rev_injective h)
      rw [if_neg h2, if_neg hi]
      by_cases hij : i = j
      · subst hij; simp
      · have h3 : ¬ j.rev = i.rev := fun h => hij (Fin.rev_injective h).symm
        simp [h3, hij]

theorem exists_eich (hσ : ∀ x, σ (σ x) = x) {p : Fin n} (hp : p ≠ p.rev) {z : Fin n → L} (hz : z p = 1)
    (hiso : ∑ c, z c * σ (z c.rev) = 0) : ∃ T : GU σ n, mat T = eichM σ p z := by
  refine exists_GU _ (Matrix.of fun i j => σ (eichM σ p z j.rev i.rev)) ?_ fun _ _ => rfl
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply, eich_dual hσ]
  by_cases hi : i = p
  · subst hi
    simp only [eichM, if_true]
    by_cases hk : k = i.rev
    · simp only [hk, if_true]
      rw [hiso, if_neg hp]
    · simp only [if_neg hk]
      by_cases hki : k = i
      · subst hki
        rw [Finset.sum_eq_single k]
        · simp [hz]
        · intro j _ hj; simp [hj]
        · simp
      · have e : ∀ j, z j * (if j = i then (if k = i then 1 else - z k) else if j = k then 1 else 0) =
            (if j = i then z i * (- z k) else 0) + (if j = k then z k else 0) := by
          intro j
          by_cases h1 : j = i
          · subst h1; simp [hki, Ne.symm hki]
          · by_cases h2 : j = k
            · subst h2; simp [h1]
            · simp [h1, h2]
        simp only [e, Finset.sum_add_distrib]
        simp [hz, Ne.symm hki]
  · have e : ∀ j, eichM σ p z i j = (if i = j then 1 else 0) +
        (if j = p.rev then (if i = p.rev then 0 else - σ (z i.rev)) else 0) := by
      intro j
      unfold eichM
      rw [if_neg hi]
      by_cases h1 : j = p.rev
      · subst h1
        by_cases h2 : i = p.rev
        · simp [h2]
        · simp [h2]
      · simp [h1]
    simp only [e, add_mul, Finset.sum_add_distrib]
    have hpr : p.rev ≠ p := Ne.symm hp
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, if_neg hpr,
      Fin.rev_rev, hz, map_one]
    by_cases hk : k = p.rev
    · subst hk
      by_cases hi' : i = p.rev
      · subst hi'; simp [hz]
      · simp [hi', hi]
    · simp [hk, hi, Ne.symm hk]

theorem eich_row_pivot (σ : L →+* L) (p : Fin n) (z : Fin n → L) (j : Fin n) : eichM σ p z p j = z j := by
  simp [eichM]

theorem eich_col_pivot (σ : L →+* L) {p : Fin n} (hp : p ≠ p.rev) {z : Fin n → L} (hz : z p = 1) (i : Fin n) :
    eichM σ p z i p = if i = p then 1 else 0 := by
  unfold eichM
  by_cases hi : i = p
  · subst hi; simp [hz]
  · simp [hi, hp]

theorem eich_fix (σ : L →+* L) {p c : Fin n} {z : Fin n → L} (hz : z p = 1) (hc : z c = 0) (hc' : z c.rev = 0) :
    (∀ j, eichM σ p z c j = if c = j then 1 else 0) ∧ (∀ i, eichM σ p z i c = if i = c then 1 else 0) := by
  have h1 : c ≠ p := by
    rintro rfl; rw [hz] at hc; exact one_ne_zero hc
  have h2 : c ≠ p.rev := by
    rintro rfl; rw [Fin.rev_rev, hz] at hc'; exact one_ne_zero hc'
  constructor
  · intro j
    unfold eichM
    rw [if_neg h1]
    by_cases hj : j = p.rev
    · subst hj; simp [h2, hc']
    · simp [hj]
  · intro i
    unfold eichM
    by_cases hi : i = p
    · subst hi; simp [hc, Ne.symm h1]
    · simp [hi, h2]

theorem eich_lower (σ : L →+* L) {p : Fin n} {z : Fin n → L} (hz : ∀ c, p < c → z c = 0) {i j : Fin n} (hij : i < j) :
    eichM σ p z i j = 0 := by
  unfold eichM
  by_cases hi : i = p
  · subst hi; rw [if_pos rfl]; exact hz j hij
  · rw [if_neg hi]
    by_cases hj : j = p.rev
    · subst hj
      rw [if_pos rfl, if_neg hij.ne, hz i.rev (Fin.lt_rev_iff.2 hij), map_zero, neg_zero]
    · rw [if_neg hj, if_neg hij.ne]

theorem inv_fix {T : GU σ n} {c : Fin n} (hr : ∀ j, mat T c j = if c = j then 1 else 0)
    (hc : ∀ i, mat T i c = if i = c then 1 else 0) :
    (∀ j, mat T⁻¹ c j = if c = j then 1 else 0) ∧ (∀ i, mat T⁻¹ i c = if i = c then 1 else 0) := by
  constructor
  · intro j
    rw [← sum_mul_inv T c j]
    simp [hr]
  · intro i
    rw [← sum_inv_mul T i c]
    simp [hc]

def IsoAt (M : Matrix (Fin n) (Fin n) L) (a c : Fin n) : Prop :=
  M a c ≠ 0 ∧ (∀ j, j ≠ c → M a j = 0) ∧ ∀ i, i ≠ a → M i c = 0

theorem IsoAt.trU {g : GU σ n} {a c : Fin n} (h : IsoAt (mat g) a c) : IsoAt (mat (trU g)) c a :=
  ⟨h.1, h.2.2, h.2.1⟩

theorem IsoAt.mul_fix {g S : GU σ n} {a c : Fin n} (h : IsoAt (mat g) a c)
    (hr : ∀ j, mat S c j = if c = j then 1 else 0) (hc : ∀ i, mat S i c = if i = c then 1 else 0) :
    IsoAt (mat (g * S)) a c := by
  have e1 : ∀ j, mat (g * S) a j = mat g a c * (if c = j then 1 else 0) := by
    intro j
    rw [mat_mul_apply, Finset.sum_eq_single c, hr]
    · intro l _ hl; rw [h.2.1 l hl, zero_mul]
    · simp
  have e2 : ∀ i, mat (g * S) i c = mat g i c := by
    intro i
    rw [mat_mul_apply]
    simp [hc]
  refine ⟨?_, fun j hj => ?_, fun i hi => ?_⟩
  · rw [e1]; simpa using h.1
  · rw [e1, if_neg (Ne.symm hj), mul_zero]
  · rw [e2, h.2.2 i hi]

theorem IsoAt.rev {g : GU σ n} {a c : Fin n} (h : IsoAt (mat g) a c) : IsoAt (mat g) a.rev c.rev := by
  have e1 : ∀ y, mat g⁻¹ y a * mat g a c = if y = c then 1 else 0 := by
    intro y
    rw [← sum_inv_mul g y c, Finset.sum_eq_single a]
    · intro l _ hl; rw [h.2.2 l hl, mul_zero]
    · simp
  have e2 : ∀ x, mat g a c * mat g⁻¹ c x = if a = x then 1 else 0 := by
    intro x
    rw [← sum_mul_inv g a x, Finset.sum_eq_single c]
    · intro l _ hl; rw [h.2.1 l hl, zero_mul]
    · simp
  have e3 : ∀ j, σ (mat g a.rev j) = mat g⁻¹ j.rev a := by
    intro j; rw [mat_inv_apply, Fin.rev_rev]
  have e4 : ∀ i, σ (mat g i c.rev) = mat g⁻¹ c i.rev := by
    intro i; rw [mat_inv_apply, Fin.rev_rev]
  refine ⟨fun h0 => ?_, fun j hj => ?_, fun i hi => ?_⟩
  · have h1 := e3 c.rev
    rw [Fin.rev_rev, h0, map_zero] at h1
    have h2 := e1 c
    rw [← h1, zero_mul, if_pos rfl] at h2
    exact zero_ne_one h2
  · have h2 := e1 j.rev
    have hne : j.rev ≠ c := fun hh => hj (by rw [← hh, Fin.rev_rev])
    rw [if_neg hne] at h2
    have h3 : mat g⁻¹ j.rev a = 0 := (mul_eq_zero.1 h2).resolve_right h.1
    rw [← e3] at h3
    exact (map_eq_zero σ).1 h3
  · have h2 := e2 i.rev
    have hne : a ≠ i.rev := fun hh => hi (by rw [hh, Fin.rev_rev])
    rw [if_neg hne] at h2
    have h3 : mat g⁻¹ c i.rev = 0 := (mul_eq_zero.1 h2).resolve_left h.1
    rw [← e4] at h3
    exact (map_eq_zero σ).1 h3

theorem clear_row {h T : GU σ n} {a p : Fin n} {u : L} (hrow : ∀ l, mat h a l = u * mat T p l) (j : Fin n) :
    mat (h * T⁻¹) a j = if p = j then u else 0 := by
  rw [mat_mul_apply]
  simp only [hrow, mul_assoc]
  rw [← Finset.mul_sum, sum_mul_inv]
  simp

def RedU (g : GU σ n) (k : ℕ) : Prop :=
  ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → ∃ c, IsoAt (mat g) b c

theorem iso_last (g : GU σ n) (a : Fin n) (h : ∀ b, b ≠ a → ∃ c, IsoAt (mat g) b c) :
    ∃ c, IsoAt (mat g) a c := by
  have hcol : ∀ c, mat g a c ≠ 0 → ∀ i, i ≠ a → mat g i c = 0 := by
    intro c hc i hi
    obtain ⟨d, hd⟩ := h i hi
    by_cases hcd : c = d
    · subst hcd; exact absurd (hd.2.2 a (Ne.symm hi)) hc
    · exact hd.2.1 c hcd
  obtain ⟨c, hc⟩ := row_ne_zero g a
  have hmul : ∀ j, mat g a j ≠ 0 → mat g⁻¹ c a * mat g a j = if c = j then 1 else 0 := by
    intro j hj
    rw [← sum_inv_mul g c j, Finset.sum_eq_single a]
    · intro l _ hl; rw [hcol j hj l hl, mul_zero]
    · simp
  refine ⟨c, ⟨hc, fun j hj => ?_, hcol c hc⟩⟩
  by_contra h0
  have h1 := hmul j h0
  rw [if_neg (Ne.symm hj)] at h1
  have h2 := hmul c hc
  rw [if_pos rfl] at h2
  have h3 : mat g⁻¹ c a = 0 := (mul_eq_zero.1 h1).resolve_right h0
  rw [h3, zero_mul] at h2
  exact zero_ne_one h2

theorem mono_end (g : GU σ n) (h : ∀ a, ∃ c, IsoAt (mat g) a c) :
    ∃ (d w : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU d ∧ IsPermW w π ∧ g = d * w := by
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have := (hf a).2.2 b (Ne.symm hne)
    rw [hab] at this
    exact (hf b).1 this
  have hrev : ∀ a, f a.rev = (f a).rev := by
    intro a
    by_contra hne
    exact (hf a).rev.1 ((hf a.rev).2.1 _ (Ne.symm hne))
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : ∀ a, π a = f a := fun _ => rfl
  obtain ⟨w, hw⟩ := exists_GU (σ := σ) (Matrix.of fun a c => if c = f a then 1 else 0)
    (Matrix.of fun i j => σ (if i.rev = f j.rev then 1 else 0)) (by
      ext i k
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      rw [Finset.sum_eq_single (f i)]
      · have : (f i).rev.rev = f i := Fin.rev_rev _
        simp only [if_true, one_mul, hrev k, Fin.rev_injective.eq_iff, hinj.eq_iff]
        by_cases hik : i = k
        · simp [hik]
        · simp [hik, Ne.symm hik]
      · intro j _ hj; simp [hj]
      · simp) (by
      intro i j
      simp)
  have hw' : ∀ a c, mat w a c = if c = f a then 1 else 0 := by
    intro a c; rw [hw]; rfl
  refine ⟨g * w⁻¹, w, π, ?_, fun a c => hw' a c, by simp⟩
  intro i j hji
  show mat (g * w⁻¹) i j = 0
  rw [mat_mul_apply, Finset.sum_eq_single (f i)]
  · rw [mat_inv_apply, hw', if_neg, map_zero, mul_zero]
    intro hh
    rw [hrev] at hh
    exact hji.ne' (hinj (Fin.rev_injective hh))
  · intro l _ hl; rw [(hf i).2.1 l hl, zero_mul]
  · simp

end Mat

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem val_div_le {x u : L} (hu : u ≠ 0) (h : Valued.v x ≤ Valued.v u) : Valued.v (x / u) ≤ 1 := by
  rw [map_div₀]
  exact div_le_one_of_le₀ h zero_le'

theorem val_div_lt {x u : L} (hu : u ≠ 0) (h : Valued.v x < Valued.v u) : Valued.v (x / u) < 1 := by
  rw [map_div₀]
  exact (div_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hu))).2 h

theorem exists_pivot (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (x : Fin n → L) (hx : ∃ c, x c ≠ 0)
    (hiso : ∑ c, x c * σ (x c.rev) = 0) :
    ∃ p, x p ≠ 0 ∧ p ≠ p.rev ∧ (∀ c, Valued.v (x c) ≤ Valued.v (x p)) ∧
      ∀ c, c < p → Valued.v (x c) < Valued.v (x p) := by
  classical
  obtain ⟨c0, hc0⟩ := hx
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun c => Valued.v (x c)) ⟨c0, Finset.mem_univ _⟩
  let P : Finset (Fin n) := Finset.univ.filter (fun c => Valued.v (x c) = Valued.v (x m))
  have hP : P.Nonempty := ⟨m, by simp [P]⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = P.min' hP := ⟨_, rfl⟩
  have hpP : Valued.v (x p) = Valued.v (x m) := by
    rw [hpdef]; exact (Finset.mem_filter.1 (P.min'_mem hP)).2
  have hmax : ∀ c, Valued.v (x c) ≤ Valued.v (x p) := fun c => hpP ▸ hm c (Finset.mem_univ c)
  have hlt : ∀ c, c < p → Valued.v (x c) < Valued.v (x p) := by
    intro c hc
    refine lt_of_le_of_ne (hmax c) fun h => ?_
    have : p ≤ c := by
      rw [hpdef]; exact P.min'_le c (by simp [P, h, hpP])
    exact absurd hc (not_lt.2 this)
  have hne : x p ≠ 0 := by
    intro h0
    have := hmax c0
    rw [h0, map_zero, le_zero_iff] at this
    exact hc0 ((Valuation.zero_iff _).1 this)
  refine ⟨p, hne, fun hp => ?_, hmax, hlt⟩
  have hM : 0 < Valued.v (x p) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)
  have hMM : Valued.v (x p) * Valued.v (x p) ≠ 0 := mul_ne_zero hM.ne' hM.ne'
  have hstrict : ∀ A B : WithZero (Multiplicative ℤ), A < Valued.v (x p) → B ≤ Valued.v (x p) →
      A * B < Valued.v (x p) * Valued.v (x p) := fun A B hA hB =>
    lt_of_le_of_lt (mul_le_mul' le_rfl hB) (mul_lt_mul_of_pos_right hA hM)
  have hrest : Valued.v (∑ c ∈ Finset.univ.erase p, x c * σ (x c.rev)) <
      Valued.v (x p) * Valued.v (x p) := by
    refine Valuation.map_sum_lt _ hMM fun c hc => ?_
    rw [map_mul, hσv]
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with h | h
    · exact hstrict _ _ (hlt c h) (hmax _)
    · have h' : c.rev < p := by
        have := Fin.rev_lt_rev.2 h
        rwa [← hp] at this
      rw [mul_comm]
      exact hstrict _ _ (hlt _ h') (hmax _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← hp] at hiso
  have e : x p * σ (x p) = - ∑ c ∈ Finset.univ.erase p, x c * σ (x c.rev) := eq_neg_of_add_eq_zero_left hiso
  have h2 : Valued.v (x p * σ (x p)) = Valued.v (x p) * Valued.v (x p) := by rw [map_mul, hσv]
  rw [e, Valuation.map_neg] at h2
  exact hrest.ne h2

theorem iso_scale {u : L} (hu : u ≠ 0) {x : Fin n → L} (h : ∑ c, x c * σ (x c.rev) = 0) :
    ∑ c, (x c / u) * σ (x c.rev / u) = 0 := by
  have hsu : σ u ≠ 0 := (map_ne_zero σ).2 hu
  have e : ∀ c, (x c / u) * σ (x c.rev / u) = (u * σ u)⁻¹ * (x c * σ (x c.rev)) := by
    intro c
    rw [map_div₀]
    field_simp
  simp only [e, ← Finset.mul_sum, h, mul_zero]

theorem eich_mem_iw (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {p : Fin n} {z : Fin n → L} {T : GU σ n}
    (hT : mat T = eichM σ p z) (h1 : ∀ c, Valued.v (z c) ≤ 1) (h2 : ∀ c, c < p → Valued.v (z c) < 1) :
    T ∈ IwU σ n := by
  refine (mem_iwU_iff hσv T).2 ⟨fun i j => ?_, fun i j hji => ?_⟩
  · show Valued.v (mat T i j) ≤ 1
    rw [hT]
    unfold eichM
    split_ifs
    · exact h1 j
    · simp
    · rw [Valuation.map_neg, hσv]; exact h1 _
    · simp
    · simp
  · show Valued.v (mat T i j) < 1
    rw [hT]
    unfold eichM
    by_cases hi : i = p
    · subst hi; rw [if_pos rfl]; exact h2 j hji
    · rw [if_neg hi]
      by_cases hj : j = p.rev
      · subst hj
        rw [if_pos rfl, if_neg hji.ne', Valuation.map_neg, hσv]
        exact h2 _ (Fin.rev_lt_iff.2 hji)
      · rw [if_neg hj, if_neg hji.ne']
        simp

theorem step (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) {k : ℕ}
    (hk : 2 * k + 1 < n) (hr : RedU g k) :
    ∃ b i g' : GU σ n, IsBorelU b ∧ i ∈ IwU σ n ∧ g = b * g' * i ∧ RedU g' (k + 1) := by
  classical
  obtain ⟨a, hav⟩ : ∃ a : Fin n, a.val = n - 1 - k := ⟨⟨n - 1 - k, by omega⟩, rfl⟩
  have ha : a ≠ a.rev := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_rev] at this
    omega
  have hfinA : ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → a ≠ b := by
    rintro b hb rfl
    omega
  have hfinR : ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → (b.rev.val < k ∨ n ≤ b.rev.val + k) := by
    intro b hb
    have := b.isLt
    rw [Fin.val_rev]
    omega
  obtain ⟨p, hxp, hp, hmax, hlt⟩ := exists_pivot hσv (mat g a) (row_ne_zero g a) (row_isotropic g ha)
  obtain ⟨u, hu⟩ : ∃ u, u = mat g a p := ⟨_, rfl⟩
  rw [← hu] at hxp
  rw [← hu] at hmax hlt
  obtain ⟨z, hz⟩ : ∃ z : Fin n → L, z = fun c => mat g a c / u := ⟨_, rfl⟩
  have hzp : z p = 1 := by rw [hz]; show mat g a p / u = 1; rw [← hu]; exact div_self hxp
  have hziso : ∑ c, z c * σ (z c.rev) = 0 := by
    rw [hz]; exact iso_scale hxp (row_isotropic g ha)
  obtain ⟨T, hT⟩ := exists_eich hσ hp hzp hziso
  have hTI : T ∈ IwU σ n := eich_mem_iw hσv hT (fun c => by rw [hz]; exact val_div_le hxp (hmax c))
    (fun c hc => by rw [hz]; exact val_div_lt hxp (hlt c hc))
  have hrow1 : ∀ l, mat g a l = u * mat T p l := by
    intro l
    rw [hT, eich_row_pivot, hz]
    show mat g a l = u * (mat g a l / u)
    field_simp
  obtain ⟨g₁, hg₁⟩ : ∃ g₁, g₁ = g * T⁻¹ := ⟨_, rfl⟩
  have h1 : ∀ j, mat g₁ a j = if p = j then u else 0 := by
    rw [hg₁]; exact clear_row hrow1
  have hfin : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c →
      mat g a c = 0 ∧ mat g a c.rev = 0 := fun b c hb hbc =>
    ⟨hbc.2.2 a (hfinA b hb), hbc.rev.2.2 a (hfinA b.rev (hfinR b hb))⟩
  have hpne : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c → p ≠ c := by
    rintro b c hb hbc rfl
    exact hxp (hu.trans (hfin b p hb hbc).1)
  have hiso1 : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c → IsoAt (mat g₁) b c := by
    intro b c hb hbc
    obtain ⟨e1, e2⟩ := hfin b c hb hbc
    have hf := eich_fix σ (c := c) hzp (by rw [hz]; simp [e1]) (by rw [hz]; simp [e2])
    rw [← hT] at hf
    obtain ⟨r, s⟩ := inv_fix hf.1 hf.2
    rw [hg₁]
    exact hbc.mul_fix r s
  obtain ⟨G, hG⟩ : ∃ G, G = trU g₁ := ⟨_, rfl⟩
  have hGe : ∀ i j, mat G i j = mat g₁ j i := by intro i j; rw [hG]; rfl
  have hGa : mat G p a = u := by rw [hGe, h1]; simp
  obtain ⟨z', hz'⟩ : ∃ z' : Fin n → L, z' = fun c => mat G p c / u := ⟨_, rfl⟩
  have hz'a : z' a = 1 := by rw [hz']; show mat G p a / u = 1; rw [hGa]; exact div_self hxp
  have hz'iso : ∑ c, z' c * σ (z' c.rev) = 0 := by
    rw [hz']; exact iso_scale hxp (row_isotropic G hp)
  have hz'0 : ∀ b : Fin n, (b.val < k ∨ n ≤ b.val + k) → z' b = 0 := by
    intro b hb
    obtain ⟨c, hbc⟩ := hr b hb
    rw [hz']
    show mat G p b / u = 0
    rw [hGe, (hiso1 b c hb hbc).2.1 p (hpne b c hb hbc), zero_div]
  obtain ⟨T', hT'⟩ := exists_eich hσ ha hz'a hz'iso
  have hrow2 : ∀ l, mat G p l = u * mat T' a l := by
    intro l
    rw [hT', eich_row_pivot, hz']
    show mat G p l = u * (mat G p l / u)
    field_simp
  obtain ⟨G₂, hG₂⟩ : ∃ G₂, G₂ = G * T'⁻¹ := ⟨_, rfl⟩
  have h2 : ∀ j, mat G₂ p j = if a = j then u else 0 := by
    rw [hG₂]; exact clear_row hrow2
  have hinvcol : ∀ i, mat T'⁻¹ i a = if i = a then 1 else 0 := by
    intro i
    rw [← sum_inv_mul T' i a]
    simp [hT', eich_col_pivot σ ha hz'a]
  have h3 : ∀ i, mat G₂ i a = mat G i a := by
    intro i
    rw [hG₂, mat_mul_apply]
    simp [hinvcol]
  obtain ⟨g₂, hg₂⟩ : ∃ g₂, g₂ = trU G₂ := ⟨_, rfl⟩
  have hg₂e : ∀ i j, mat g₂ i j = mat G₂ j i := by intro i j; rw [hg₂]; rfl
  have hIso : IsoAt (mat g₂) a p := by
    refine ⟨?_, fun j hj => ?_, fun i hi => ?_⟩
    · rw [hg₂e, h2, if_pos rfl]; exact hxp
    · rw [hg₂e, h3, hGe, h1, if_neg (Ne.symm hj)]
    · rw [hg₂e, h2, if_neg (Ne.symm hi)]
  have hiso2 : ∀ b c, (b.val < k ∨ n ≤ b.val + k) → IsoAt (mat g) b c → IsoAt (mat g₂) b c := by
    intro b c hb hbc
    have hf := eich_fix σ (c := b) hz'a (hz'0 b hb) (hz'0 b.rev (hfinR b hb))
    rw [← hT'] at hf
    obtain ⟨r, s⟩ := inv_fix hf.1 hf.2
    have i1 : IsoAt (mat G) c b := by rw [hG]; exact (hiso1 b c hb hbc).trU
    have i2 := i1.mul_fix r s
    rw [← hG₂] at i2
    rw [hg₂]
    exact i2.trU
  have hB : IsBorelU (trU T') := by
    intro i j hji
    show mat T' j i = 0
    rw [hT']
    refine eich_lower σ (fun c hc => hz'0 c (Or.inr ?_)) hji
    have := Fin.lt_def.1 hc
    omega
  refine ⟨trU T', T, g₂, hB, hTI, ?_, fun b hb => ?_⟩
  · have e : trU T' * g₂ = g₁ := by
      rw [hg₂, hG₂, trU_mul, ← mul_assoc, ← trU_mul, inv_mul_cancel, trU_one, one_mul, hG, trU_trU]
    rw [e, hg₁, inv_mul_cancel_right]
  · by_cases hbk : b.val < k ∨ n ≤ b.val + k
    · obtain ⟨c, hc⟩ := hr b hbk
      exact ⟨c, hiso2 b c hbk hc⟩
    · have : b = a ∨ b = a.rev := by
        have := b.isLt
        simp only [Fin.ext_iff, Fin.val_rev]
        omega
      rcases this with rfl | rfl
      · exact ⟨p, hIso⟩
      · exact ⟨p.rev, hIso.rev⟩

theorem reduce (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) (k : ℕ)
    (hk : 2 * k ≤ n) : ∃ b i g' : GU σ n, IsBorelU b ∧ i ∈ IwU σ n ∧ g = b * g' * i ∧ RedU g' k := by
  induction k with
  | zero =>
    refine ⟨1, 1, g, Formalism.UG.P.fSatake_borel_one, one_mem _, by simp, fun b hb => ?_⟩
    have := b.isLt
    omega
  | succ k ih =>
    obtain ⟨b, i, g', hb, hi, e, hr⟩ := ih (by omega)
    obtain ⟨b', i', g'', hb', hi', e', hr'⟩ := step hσ hσv g' (by omega) hr
    refine ⟨b * b', i' * i, g'', Formalism.UG.P.fSatake_borel_mul hb hb', mul_mem hi' hi, ?_, hr'⟩
    rw [e, e']
    simp only [mul_assoc]

end Val

theorem bruhat_iwasawa : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ g : GU σ n,
    ∃ (b w i : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU b ∧ IsPermW w π ∧ i ∈ IwU σ n ∧ g = b * w * i := by
  intro L _ _ σ n hσ hσv g
  obtain ⟨b, i, g', hb, hi, e, hr⟩ := reduce hσ hσv g (n / 2) (by omega)
  have hall : ∀ a, ∃ c, IsoAt (mat g') a c := by
    intro a
    by_cases ha : a.val < n / 2 ∨ n ≤ a.val + n / 2
    · exact hr a ha
    · refine iso_last g' a fun b hb => hr b ?_
      have h1 : b.val ≠ a.val := fun h => hb (Fin.ext h)
      have := b.isLt
      omega
  obtain ⟨d, w, π, hd, hw, e'⟩ := mono_end g' hall
  refine ⟨b * d, w, i, π, Formalism.UG.P.fSatake_borel_mul hb hd, hw, hi, ?_⟩
  rw [e, e']
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.BruhatIw

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwasawa_bruhat_decomposition : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ g : GU σ n, ∃ (b w i : GU σ n) (π : Equiv.Perm (Fin n)), IsBorelU b ∧ IsPermW w π ∧ i ∈ IwU σ n ∧ g = b * w * i := by
  atlas_forward_decl GlobalTheory.CompanionTheory.BruhatIw.bruhat_iwasawa
end

section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_weight_decreases : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t w w' b r i : GU σ n) (π π' : Equiv.Perm (Fin n)), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → IsPermW w π → IsPermW w' π' → IsBorelU b → r ∈ IwU σ n → i ∈ IwU σ n → w * r * t = b * w' * i → permWt t π' < permWt t π ∨ (π' = π ∧ ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = ordL (((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a))) := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.cell_triang | exact GlobalTheory.CompanionTheory.SatPow.cell_triang | (intros; apply GlobalTheory.CompanionTheory.SatPow.cell_triang <;> assumption)
end

section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_factorization : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → ∀ i ∈ IwU σ n, ∃ u ∈ IwU σ n, IsUnipU u ∧ ∃ y ∈ IwU σ n, t⁻¹ * y * t ∈ IwU σ n ∧ i = u * y := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact | exact GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact | (intros; apply GlobalTheory.CompanionTheory.SatPow.IwFact.iwahori_fact <;> assumption)
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem isOpen_iwU {σ : L →+* L} {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) :
    IsOpen (IwU σ n : Set (GU σ n)) := by
  have hc : ∀ i j : Fin n, Continuous fun g : GU σ n =>
      ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j := fun i j =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hle : IsOpen {x : L | Valued.v x ≤ 1} := by
    convert Valued.isOpen_integer (Γ₀ := WithZero (Multiplicative ℤ)) L using 1
    ext x
    exact (Valuation.mem_integer_iff (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) x).symm
  have hlt : IsOpen {x : L | Valued.v x < 1} := by
    convert Valued.isOpen_ball L 1 using 2 with x
    simp only [Valuation.restrict_lt_one_iff]
  have hset : (IwU σ n : Set (GU σ n)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ({g : GU σ n | Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1} ∩
         {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1}) := by
    ext g
    simp only [SetLike.mem_coe, mem_iwU_iff hσv g, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ i j
      exact ⟨h1 i j, h2 i j⟩
    · intro h
      exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  refine (hle.preimage (hc i j)).inter ?_
  by_cases hij : j < i
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        (fun g : GU σ n => ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ⁻¹'
          {x : L | Valued.v x < 1} := by
      ext g
      simp [hij]
    rw [e]
    exact hlt.preimage (hc i j)
  · have e : {g : GU σ n | j < i → Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) < 1} =
        Set.univ := by
      ext g
      simp [hij]
    rw [e]
    exact isOpen_univ

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsOpen (H : Set G)) (t : G) :
    IsOpen ((H.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have e : ⇑(MulAut.conj t).toMonoidHom = fun x => t * x * t⁻¹ := by
    funext x
    simp [MulAut.conj_apply]
  rw [e]
  have h1 : IsOpenMap fun x : G => t * x * t⁻¹ :=
    (isOpenMap_mul_right t⁻¹).comp (isOpenMap_mul_left t)
  exact h1 _ hH

theorem finite_index_iwU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q →
      Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧
      ∀ t : GU σ n, Finite (IwU σ n ⧸
        (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  intro L _ _ _ ϖ σ q n h
  obtain ⟨-, hKc, hle, -⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n h
  have hIo : IsOpen (IwU σ n : Set (GU σ n)) := isOpen_iwU h.2.1
  haveI : CompactSpace (KU σ n) := isCompact_iff_compactSpace.mp hKc
  refine ⟨Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hIo), fun t => ?_⟩
  have hIc : IsCompact (IwU σ n : Set (GU σ n)) :=
    hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hIo) fun x hx => hle hx
  haveI : CompactSpace (IwU σ n) := isCompact_iff_compactSpace.mp hIc
  have hOpen : IsOpen ((IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom : Subgroup (GU σ n)) :
      Set (GU σ n)) := by
    rw [Subgroup.coe_inf]
    exact hIo.inter (isOpen_map_conj hIo t)
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen _ _ hOpen)

end GlobalTheory.CompanionTheory.SatPow

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_iwahori_index_finite : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Finite (KU σ n ⧸ (IwU σ n).subgroupOf (KU σ n)) ∧ ∀ t : GU σ n, Finite (IwU σ n ⧸ (IwU σ n ⊓ (IwU σ n).map (MulAut.conj t).toMonoidHom).subgroupOf (IwU σ n)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SatPow.finite_index_iwU
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

section Contr

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem val_le_of_ordL_lt {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) (h : ordL a < ordL b) :
    Valued.v b ≤ Valued.v a := by
  have ha' : Valued.v a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hb' : Valued.v b ≠ 0 := (Valuation.ne_zero_iff _).2 hb
  unfold ordL at h
  rw [dif_neg ha', dif_neg hb'] at h
  have hle : WithZero.unzero hb' ≤ WithZero.unzero ha' := by
    rw [← Multiplicative.toAdd_le]; omega
  have := WithZero.coe_le_coe.2 hle
  rwa [WithZero.coe_unzero, WithZero.coe_unzero] at this

theorem conj_entries_le_one {t A : GL (Fin n) L} (ht : IsDiagM t) (hd : IsStrictDom t)
    (h1 : ∀ i j, Valued.v ((A : Matrix (Fin n) (Fin n) L) i j) ≤ 1)
    (h2 : ∀ i j, j < i → (A : Matrix (Fin n) (Fin n) L) i j = 0)
    (h3 : ∀ i, (A : Matrix (Fin n) (Fin n) L) i i = 1) (k : ℕ) (i j : Fin n) :
    Valued.v (((t ^ k * A * (t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
  set d : Fin n → L := fun i => (t : Matrix (Fin n) (Fin n) L) i i with hdef
  have htd : (t : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hdef]
    · rw [Matrix.diagonal_apply_ne _ hab]; exact ht a b hab
  have hd0 : ∀ a, d a ≠ 0 := by
    intro a h0
    have hm : ((t : Matrix (Fin n) (Fin n) L) * ((t⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) a a = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]; simp
    rw [htd, Matrix.diagonal_mul, h0, zero_mul] at hm
    exact zero_ne_one hm
  have hpow : ((t ^ k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => d a ^ k := by
    rw [Units.val_pow_eq_pow_val, htd, Matrix.diagonal_pow]
    rfl
  have hinv : (((t ^ k)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun a => (d a ^ k)⁻¹ := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hpow, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (pow_ne_zero _ (hd0 a))
  rw [Units.val_mul, Units.val_mul, hpow, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hle : Valued.v (d i) ≤ Valued.v (d j) := val_le_of_ordL_lt (hd0 j) (hd0 i) (hd i j hij)
    have hb : Valued.v (d j) ^ k ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff _).2 (hd0 j))
    rw [map_mul, map_mul, map_inv₀, map_pow, map_pow]
    calc Valued.v (d i) ^ k * Valued.v ((A : Matrix (Fin n) (Fin n) L) i j) * (Valued.v (d j) ^ k)⁻¹
        ≤ Valued.v (d i) ^ k * 1 * (Valued.v (d j) ^ k)⁻¹ := by gcongr; exact h1 i j
      _ = Valued.v (d i) ^ k / Valued.v (d j) ^ k := by rw [mul_one, div_eq_mul_inv]
      _ ≤ 1 := (div_le_one₀ (zero_lt_iff.2 hb)).2 (pow_le_pow_left' hle k)
  · subst hij
    rw [h3, mul_one, mul_inv_cancel₀ (pow_ne_zero _ (hd0 i)), map_one]
  · rw [h2 i j hij]; simp

theorem conj_unip_mem_KU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u →
      ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  intro L _ _ σ n t u ht hd hu hU k
  have hinv := (GlobalTheory.LGrp.mem_GU_iff σ n (u : GL (Fin n) L)).1 u.2
  have huGL : (u : GL (Fin n) L) ∈ IwGL L n := hu
  have hU1 : ∀ i j, Valued.v (((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 :=
    fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries huGL i j
  have hV1 : ∀ i j, Valued.v ((((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 :=
    fun i j => GlobalTheory.CompanionTheory.KUFactsU.iwGL_entries (inv_mem huGL) i j
  have hV2 : ∀ i j, j < i → (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
    intro i j hji
    rw [hinv, hU.1 _ _ (Fin.rev_lt_rev.2 hji), map_zero]
  have hV3 : ∀ i, (((u : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    intro i
    rw [hinv, hU.2, map_one]
  have hmem : t ^ k * u * (t ^ k)⁻¹ ∈ (KU σ n : Set (GU σ n)) := by
    rw [IntPtsUnitary.coe_KU, Set.mem_preimage, IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact conj_entries_le_one ht hd hU1 hU.1 hU.2 k i j
    · have e : (((t ^ k * u * (t ^ k)⁻¹ : GU σ n) : GL (Fin n) L))⁻¹ =
          (t : GL (Fin n) L) ^ k * (u : GL (Fin n) L)⁻¹ * ((t : GL (Fin n) L) ^ k)⁻¹ := by
        simp [mul_assoc]
      rw [e]
      exact conj_entries_le_one ht hd hV1 hV2 hV3 k i j
  exact hmem

end Contr

end GlobalTheory.CompanionTheory.SatPow

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_conjugate_unipotent_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u → ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow.RepsGen

private theorem mem_map_conj_iff_inv_mul_mul_mem {G : Type*} [Group G] (I : Subgroup G) (t y : G) :
    y ∈ I.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨t⁻¹ * y * t, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem reps_of_quotient_with_property (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop)
    (hP1 : P 1)
    (hfin : Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I))
    (hfac : ∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) :
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧
      ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  classical
  set H := (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I with hH
  have : Fintype (I ⧸ H) := @Fintype.ofFinite _ hfin
  have hmem : ∀ a b : I, (QuotientGroup.mk a : I ⧸ H) = QuotientGroup.mk b ↔
      t⁻¹ * ((a : G)⁻¹ * b) * t ∈ I := by
    intro a b
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      and_iff_right (a⁻¹ * b).2, mem_map_conj_iff_inv_mul_mul_mem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have key : ∀ c : I ⧸ H, ∃ r : I, P r ∧ (QuotientGroup.mk r : I ⧸ H) = c ∧
      (c = QuotientGroup.mk 1 → r = 1) := by
    intro c
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective c
    by_cases h : (QuotientGroup.mk i : I ⧸ H) = QuotientGroup.mk 1
    · exact ⟨1, by simpa using hP1, h.symm, fun _ => rfl⟩
    · obtain ⟨u, hu, hPu, y, hy, hty, hi⟩ := hfac i i.2
      refine ⟨⟨u, hu⟩, hPu, ?_, fun h' => absurd h' h⟩
      rw [hmem]
      have hy' : u⁻¹ * (i : G) = y := by rw [hi, inv_mul_cancel_left]
      show t⁻¹ * (u⁻¹ * (i : G)) * t ∈ I
      rw [hy']
      exact hty
  choose f hfP hfmk hf1 using key
  refine ⟨Finset.univ.image (fun c => (f c : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨QuotientGroup.mk 1, Finset.mem_univ _, by rw [hf1 _ rfl]; simp⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨(f c).2, hfP c⟩
  · intro i hi
    refine ⟨f (QuotientGroup.mk ⟨i, hi⟩),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (hmem (f (QuotientGroup.mk ⟨i, hi⟩)) ⟨i, hi⟩).1 (hfmk _)
    · rintro r ⟨hr, hri⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
      have hc : c = QuotientGroup.mk ⟨i, hi⟩ := (hfmk c).symm.trans ((hmem _ _).2 hri)
      subst hc
      rfl

end GlobalTheory.CompanionTheory.SatPow.RepsGen
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_reps_of_factorization : ∀ (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop), P 1 → Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I) → (∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) → ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧ ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow

theorem functional_eq_zero_of_late_iterates :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  intro V _ _ _ A hA l v j₀ h
  let U : Submodule ℂ V := Submodule.span ℂ (Set.range fun i : ℕ => (A ^ (i + j₀)) v)
  have hUl : U ≤ LinearMap.ker l := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (h (i + j₀) (Nat.le_add_left j₀ i))
  have hle : U ≤ U.comap A := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    have e : A ((A ^ (i + j₀)) v) = (A ^ ((i + 1) + j₀)) v := by
      rw [show i + 1 + j₀ = (i + j₀) + 1 by omega, pow_succ', Module.End.mul_apply]
    show A ((A ^ (i + j₀)) v) ∈ U
    rw [e]
    exact Submodule.subset_span ⟨i + 1, rfl⟩
  have hAU : ∀ u ∈ U, A u ∈ U := fun u hu => hle hu
  let B : U →ₗ[ℂ] U := A.restrict hAU
  have hBi : Function.Injective B := by
    intro x y hxy
    apply Subtype.ext
    apply hA
    have := congrArg Subtype.val hxy
    simpa [B, LinearMap.restrict_apply] using this
  have hBs : Function.Surjective B := LinearMap.injective_iff_surjective.mp hBi
  have pull : ∀ x : V, A x ∈ U → x ∈ U := by
    intro x hx
    obtain ⟨u, hu⟩ := hBs ⟨A x, hx⟩
    have hux : A u = A x := congrArg Subtype.val hu
    rw [← hA hux]
    exact u.2
  have key : ∀ k : ℕ, (A ^ (j₀ - k)) v ∈ U := by
    intro k
    induction k with
    | zero =>
      have e0 : (A ^ (j₀ - 0)) v = (A ^ (0 + j₀)) v := by rw [Nat.sub_zero, Nat.zero_add]
      rw [e0]
      exact Submodule.subset_span ⟨0, rfl⟩
    | succ k ih =>
      rcases Nat.eq_zero_or_pos (j₀ - k) with h0 | hpos
      · have e1 : j₀ - (k + 1) = j₀ - k := by omega
        rw [e1]
        exact ih
      · have e : j₀ - k = (j₀ - (k + 1)) + 1 := by omega
        have e2 : (A ^ (j₀ - k)) v = A ((A ^ (j₀ - (k + 1))) v) := by
          rw [e, pow_succ', Module.End.mul_apply]
        rw [e2] at ih
        exact pull _ ih
  have hv : v ∈ U := by
    have h1 := key j₀
    rwa [Nat.sub_self, pow_zero, Module.End.one_apply] at h1
  exact LinearMap.mem_ker.mp (hUl hv)

end GlobalTheory.CompanionTheory.SatPow
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_zero_of_injective_power : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.HeckeTrace

variable {G : Type} [Group G]

theorem aOp_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) : ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g :=
  _root_.UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant hR hu hφ

theorem aOp_iterate_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) (j : ℕ) :
    ∀ g, ∀ i ∈ I, (aOp R t)^[j] φ (g * i) = (aOp R t)^[j] φ g := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact aOp_rightInvariant hR hu ih

theorem exists_words (K : Subgroup G) (t : G) (R : Finset G) (h1 : (1 : G) ∈ R)
    (hc : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) (j : ℕ) :
    ∃ W : Multiset G, W ≠ 0 ∧ (∀ w ∈ W, ∃ k ∈ K, w = k * t ^ j) ∧
      ∀ (ψ : G → ℂ) (g : G), (aOp R t)^[j] ψ g = (W.map fun w => ψ (g * w)).sum := by
  induction j with
  | zero =>
    refine ⟨{1}, by simp, ?_, fun ψ g => by simp⟩
    intro w hw
    exact ⟨1, one_mem K, by simpa using hw⟩
  | succ j ih =>
    obtain ⟨W, hW0, hWK, hWf⟩ := ih
    refine ⟨W.bind fun w => R.val.map fun r => w * r * t, ?_, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
      intro h0
      have hm : w * 1 * t ∈ W.bind fun w => R.val.map fun r => w * r * t :=
        Multiset.mem_bind.2 ⟨w, hw, Multiset.mem_map.2 ⟨1, h1, rfl⟩⟩
      rw [h0] at hm
      exact Multiset.notMem_zero _ hm
    · intro x hx
      obtain ⟨w, hw, hx⟩ := Multiset.mem_bind.1 hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := hWK w hw
      refine ⟨k * (t ^ j * r * (t ^ j)⁻¹), mul_mem hk (hc r hr j), ?_⟩
      rw [pow_succ]
      group
    · intro ψ g
      rw [Function.iterate_succ_apply, hWf, Multiset.map_bind, Multiset.sum_bind]
      congr 1
      refine Multiset.map_congr rfl fun w _ => ?_
      rw [Multiset.map_map]
      show ∑ r ∈ R, ψ (g * w * r * t) = _
      simp only [Function.comp, mul_assoc]
      rfl

theorem finsum_left_mul {K I : Subgroup G} (hIK : I ≤ K) {φ : G → ℂ} (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g)
    {k : G} (hk : k ∈ K) :
    ∑ᶠ c : K ⧸ I.subgroupOf K, φ (k * ((c.out : K) : G)) = ∑ᶠ c : K ⧸ I.subgroupOf K, φ ((c.out : K) : G) := by
  let kk : K := ⟨k, hk⟩
  rw [← finsum_comp_equiv (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K))
    (f := fun c : K ⧸ I.subgroupOf K => φ ((c.out : K) : G))]
  refine finsum_congr fun c => ?_
  have e : (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c = ((kk * c.out : K) : K ⧸ I.subgroupOf K) := by
    show kk • c = _
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (I.subgroupOf K) (kk * c.out)
  have hi : ((h : K) : G) ∈ I := Subgroup.mem_subgroupOf.1 h.2
  show _ = φ ((((MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c).out : K) : G)
  rw [e, hh]
  show _ = φ (k * ((c.out : K) : G) * ((h : K) : G))
  rw [hφ _ _ hi]

theorem multiset_sum_eq_hAct (K : Subgroup G) (s : G) (M : Multiset G) (hM0 : M ≠ 0)
    (hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G))
    (hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum) :
    ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = (m : ℂ) * hAct K (dosetInd ℂ K s) ψ 1 := by
  classical
  set M' : Multiset (G ⧸ K) := M.map (QuotientGroup.mk : G → G ⧸ K) with hM'
  have hout : ∀ (ψ : G → ℂ), (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ x : G,
      ψ ((x : G ⧸ K).out) = ψ x := by
    intro ψ hψ x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hh, hψ _ _ h.2]
  have key1 : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = ∑ y ∈ M'.toFinset, (M'.count y : ℂ) * ψ y.out := by
    intro ψ hψ
    have e : M.map ψ = M'.map fun y : G ⧸ K => ψ y.out := by
      rw [hM', Multiset.map_map]
      exact Multiset.map_congr rfl fun x _ => (hout ψ hψ x).symm
    rw [e, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
  let e : G ⧸ K → G → ℂ := fun y x => if (x : G ⧸ K) = y then 1 else 0
  have he : ∀ y g, ∀ k ∈ K, e y (g * k) = e y g := by
    intro y g k hk
    have : ((g * k : G) : G ⧸ K) = g := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hk
    simp only [e, this]
  have key2 : ∀ y, (M.map (e y)).sum = (M'.count y : ℂ) := by
    intro y
    rw [key1 _ (he y)]
    have : ∀ z : G ⧸ K, (M'.count z : ℂ) * e y z.out = if z = y then (M'.count z : ℂ) else 0 := by
      intro z
      simp only [e, QuotientGroup.out_eq']
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : M'.count y = 0 := Multiset.count_eq_zero.2 (by simpa using h)
      simp [this]
  have key3 : ∀ k ∈ K, ∀ g : G, M'.count ((k * g : G) : G ⧸ K) = M'.count (g : G ⧸ K) := by
    intro k hk g
    have h1 := hinv (e ((k * g : G) : G ⧸ K)) (he _) k hk
    have h2 : (fun x => e ((k * g : G) : G ⧸ K) (k * x)) = e (g : G ⧸ K) := by
      funext x
      have : ((k * x : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) ↔ (x : G ⧸ K) = (g : G ⧸ K) := by
        rw [QuotientGroup.eq, QuotientGroup.eq]
        have : (k * x)⁻¹ * (k * g) = x⁻¹ * g := by group
        rw [this]
      simp only [e, this]
    rw [h2, key2, key2] at h1
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hM0
  have hconst : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
      M'.count (g : G ⧸ K) = M'.count (x0 : G ⧸ K) := by
    have hred : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
        M'.count (g : G ⧸ K) = M'.count (s : G ⧸ K) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      have : ((a * s * b : G) : G ⧸ K) = ((a * s : G) : G ⧸ K) := by
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem hb
      rw [this, key3 a ha]
    intro g hg
    rw [hred g hg, hred x0 (hMs x0 hx0)]
  have hpos : 0 < M'.count (x0 : G ⧸ K) :=
    Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hx0)
  refine ⟨M'.count (x0 : G ⧸ K), hpos, fun ψ hψ => ?_⟩
  have hmem : ∀ y : G ⧸ K, y ∈ M'.toFinset ↔ y.out ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hy)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
      obtain ⟨a, ha, b, hb, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hMs x hx)
      refine DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * h, mul_mem hb h.2, ?_⟩
      rw [hh, e1]
      group
    · intro hy
      have h := hconst _ hy
      rw [QuotientGroup.out_eq'] at h
      refine Multiset.mem_toFinset.2 (Multiset.count_pos.1 ?_)
      rw [h]
      exact hpos
  have hact : hAct K (dosetInd ℂ K s) ψ 1 = ∑ y ∈ M'.toFinset, ψ y.out := by
    unfold hAct
    rw [finsum_eq_sum_of_support_subset (s := M'.toFinset)]
    · refine Finset.sum_congr rfl fun y hy => ?_
      have h := (hmem y).1 hy
      simp [dosetInd, Set.indicator_of_mem h]
    · intro y hy
      by_contra hn
      have h : y.out ∉ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := fun h => hn ((hmem y).2 h)
      apply hy
      simp [dosetInd, Set.indicator_of_notMem h]
  rw [hact, key1 ψ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hconst _ ((hmem y).1 hy)
  rw [QuotientGroup.out_eq'] at h
  rw [h]

theorem heckeTrace : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  intro G _ K I hIK hfin t R h1 hR hc hu j
  classical
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  obtain ⟨W, hW0, hWK, hWf⟩ := exists_words K t R h1 hc j
  set M : Multiset G := (Finset.univ : Finset (K ⧸ I.subgroupOf K)).val.bind
    fun c => W.map fun w => ((c.out : K) : G) * w with hMdef
  have hM : ∀ φ : G → ℂ, (M.map φ).sum =
      ∑ c : K ⧸ I.subgroupOf K, (W.map fun w => φ (((c.out : K) : G) * w)).sum := by
    intro φ
    rw [hMdef, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_map, Function.comp_def]
    rfl
  have hL : ∀ ψ : G → ℂ, ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (M.map ψ).sum := by
    intro ψ
    rw [finsum_eq_sum_of_fintype, hM]
    exact Finset.sum_congr rfl fun c _ => hWf ψ _
  have hIinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ g, ∀ i ∈ I, ψ (g * i) = ψ g :=
    fun ψ hψ g i hi => hψ g i (hIK hi)
  have hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum := by
    intro ψ hψ k hk
    rw [← hL ψ, ← finsum_left_mul hIK (aOp_iterate_rightInvariant hR hu (hIinv ψ hψ) j) hk,
      finsum_eq_sum_of_fintype, hM]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWf ψ]
    simp only [mul_assoc]
  have hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset (t ^ j) (K : Set G) (K : Set G) := by
    intro x hx
    obtain ⟨c, -, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨k, hk, rfl⟩ := hWK w hw
    exact DoubleCoset.mem_doubleCoset.2
      ⟨((c.out : K) : G) * k, mul_mem (c.out : K).2 hk, 1, one_mem K, by simp [mul_assoc]⟩
  have hM0 : M ≠ 0 := by
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
    let c0 : K ⧸ I.subgroupOf K := ((1 : K) : K ⧸ I.subgroupOf K)
    intro h0
    have hm : ((c0.out : K) : G) * w ∈ M :=
      Multiset.mem_bind.2 ⟨c0, Finset.mem_univ c0, Multiset.mem_map.2 ⟨w, hw, rfl⟩⟩
    rw [h0] at hm
    exact Multiset.notMem_zero _ hm
  obtain ⟨m, hm, hmf⟩ := multiset_sum_eq_hAct K (t ^ j) M hM0 hMs hinv
  exact ⟨m, hm, fun ψ hψ => by rw [hL, hmf ψ hψ]⟩

end GlobalTheory.CompanionTheory.SatPow.HeckeTrace

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_power_coset_formula : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow

theorem aOp_rightInv {G : Type} [Group G] (I : Subgroup G) (t : G) (R : Finset G) (hRI : ∀ r ∈ R, r ∈ I)
    (hR : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) (φ : G → ℂ) (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) :
    ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g := by
  classical
  intro g i hi
  have key : ∀ r, r ∈ R → ∃ r', r' ∈ R ∧ t⁻¹ * (r'⁻¹ * (i * r)) * t ∈ I := fun r hr => by
    obtain ⟨r', h, -⟩ := hR (i * r) (I.mul_mem hi (hRI r hr))
    exact ⟨r', h⟩
  choose! f hfR hf using key
  have he : ∀ r ∈ R, φ (g * i * r * t) = φ (g * f r * t) := fun r hr => by
    have e : g * i * r * t = (g * f r * t) * (t⁻¹ * ((f r)⁻¹ * (i * r)) * t) := by group
    rw [e, hφ _ _ (hf r hr)]
  have hinj : Set.InjOn f (R : Set G) := fun r₁ h₁ r₂ h₂ e => by
    have h3 : t⁻¹ * (r₁⁻¹ * r₂) * t ∈ I := by
      have := I.mul_mem (I.inv_mem (hf r₁ h₁)) (hf r₂ h₂)
      rw [← e] at this
      have e2 : (t⁻¹ * ((f r₁)⁻¹ * (i * r₁)) * t)⁻¹ * (t⁻¹ * ((f r₁)⁻¹ * (i * r₂)) * t) = t⁻¹ * (r₁⁻¹ * r₂) * t := by
        group
      rwa [e2] at this
    exact (hR r₂ (hRI r₂ h₂)).unique ⟨h₁, h3⟩ ⟨h₂, by simp [I.one_mem]⟩
  have himg : R.image f = R :=
    Finset.eq_of_subset_of_card_le (fun x hx => by
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      exact hfR r hr) (by rw [Finset.card_image_of_injOn hinj])
  unfold aOp
  rw [Finset.sum_congr rfl he]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image hinj]

theorem abs_main {G : Type} [Group G] (K I : Subgroup G) (hIK : I ≤ K) (hfin : Finite (K ⧸ I.subgroupOf K)) (t : G)
    (R : Finset G) (h1R : (1 : G) ∈ R) (hRI : ∀ r ∈ R, r ∈ I) (hRt : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K)
    (hR : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I)
    (Wsp : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ Wsp]
    (hWA : ∀ φ ∈ Wsp, aOp R t φ ∈ Wsp) (hinj : ∀ φ ∈ Wsp, aOp R t φ = 0 → φ = 0)
    (φ₀ : G → ℂ) (hφ₀ : φ₀ ∈ Wsp) (hK : ∀ g, ∀ k ∈ K, φ₀ (g * k) = φ₀ g) (h1 : φ₀ 1 = 1)
    (lam : ℕ → ℂ) (hlam : ∀ j, hAct K (dosetInd ℂ K (t ^ j)) φ₀ 1 = lam j) (j₀ : ℕ) : ∃ j ≥ j₀, lam j ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  let A : Wsp →ₗ[ℂ] Wsp :=
    { toFun := fun φ => ⟨aOp R t φ, hWA φ φ.2⟩
      map_add' := fun a b => Subtype.ext (by
        funext g; simp [aOp, Finset.sum_add_distrib])
      map_smul' := fun c a => Subtype.ext (by
        funext g; simp [aOp, Finset.mul_sum]) }
  let l : Wsp →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ c : K ⧸ I.subgroupOf K, (φ : G → ℂ) ((c.out : K) : G)
      map_add' := fun a b => by simp [Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.mul_sum] }
  let v : Wsp := ⟨φ₀, hφ₀⟩
  have hAj : ∀ j, (((A ^ j) v : Wsp) : G → ℂ) = (aOp R t)^[j] φ₀ := fun j => by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply']
      show aOp R t (((A ^ j) v : Wsp) : G → ℂ) = _
      rw [ih]
  have hAinj : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact Subtype.ext (hinj a a.2 (congrArg Subtype.val ha))
  have hl0 : l v = 0 := by
    refine GlobalTheory.T.functional_zero_of_injective_power _ A hAinj l v j₀ fun j hj => ?_
    obtain ⟨m, -, hm⟩ := GlobalTheory.T.hecke_power_coset_formula G K I hIK hfin t R h1R hRI hRt hR j
    have := hm φ₀ hK
    rw [hlam, hcon j hj, mul_zero, finsum_eq_sum_of_fintype] at this
    show ∑ c : K ⧸ I.subgroupOf K, (((A ^ j) v : Wsp) : G → ℂ) ((c.out : K) : G) = 0
    rw [hAj, this]
  have hl1 : l v = (Fintype.card (K ⧸ I.subgroupOf K) : ℂ) := by
    show ∑ c : K ⧸ I.subgroupOf K, φ₀ ((c.out : K) : G) = _
    have : ∀ c : K ⧸ I.subgroupOf K, φ₀ ((c.out : K) : G) = 1 := fun c => by
      have := hK 1 _ (c.out : K).2
      rwa [one_mul, h1] at this
    simp [this]
  rw [hl1] at hl0
  exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 hl0)

section U

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem isPermW_unique {w w' : GU σ n} {π : Equiv.Perm (Fin n)} (h : IsPermW w π) (h' : IsPermW w' π) : w = w' :=
  Subtype.ext (Units.ext (Matrix.ext fun a c => by rw [h a c, h' a c]))

theorem chiDeltaU_congr {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {b b' : GU σ n}
    (h : ∀ a : Fin n, ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) =
      ordL (((b' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) : chiDeltaU q α b = chiDeltaU q α b' := by
  unfold chiDeltaU
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [h]
  · rfl

theorem chiDeltaU_ne_zero {m : ℕ} {q : ℕ} (hq : (q : ℂ) ≠ 0) {α : Fin m → ℂ} (hα : ∀ i, α i ≠ 0) (b : GU σ n) :
    chiDeltaU q α b ≠ 0 := by
  unfold chiDeltaU
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  split_ifs with hi
  · exact mul_ne_zero (zpow_ne_zero _ (hα i)) (zpow_ne_zero _ hq)
  · exact one_ne_zero

theorem conj_diag {t w : GU σ n} {π : Equiv.Perm (Fin n)} (ht : IsDiagM (t : GL (Fin n) L)) (hw : IsPermW w π) :
    IsBorelU (w * t * w⁻¹) ∧ ∀ a : Fin n, (((w * t * w⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π a) := by
  set s := w * t * w⁻¹ with hs
  have hsw : (((s * w : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (((w * t : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    rw [hs]; congr 2; group
  have key : ∀ a e : Fin n, ((s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a e =
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (π a) (π e) := fun a e => by
    have := congrFun (congrFun hsw a) (π e)
    simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply] at this
    simpa [hw _ _] using this
  refine ⟨fun i j hij => ?_, fun a => key a a⟩
  rw [key]
  exact ht _ _ fun h => (ne_of_gt hij) (π.injective h)

theorem aOp_inj (q : ℕ) (hq : (q : ℂ) ≠ 0) {m : ℕ} (α : Fin m → ℂ) (hα : ∀ i, α i ≠ 0)
    (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : GU σ n) (htD : IsDiagM (t : GL (Fin n) L)) (htS : IsStrictDom (t : GL (Fin n) L))
    (R : Finset (GU σ n)) (h1R : (1 : GU σ n) ∈ R) (hRI : ∀ r ∈ R, r ∈ IwU σ n)
    (φ : GU σ n → ℂ) (hB : ∀ b g, IsBorelU b → φ (b * g) = chiDeltaU q α b * φ g)
    (hI : ∀ g, ∀ i ∈ IwU σ n, φ (g * i) = φ g) (h0 : aOp R t φ = 0) : φ = 0 := by
  classical
  by_contra hne
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hdec : ∀ b w i : GU σ n, IsBorelU b → i ∈ IwU σ n → φ (b * w * i) = chiDeltaU q α b * φ w :=
    fun b w i hb hi => by rw [hI _ _ hi, hB _ _ hb]
  set S : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun π => ∃ w : GU σ n, IsPermW w π ∧ φ w ≠ 0 with hS
  have hSne : S.Nonempty := by
    obtain ⟨b, w, i, π, hb, hw, hi, e⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv g
    refine ⟨π, Finset.mem_filter.2 ⟨Finset.mem_univ _, w, hw, fun h => hg ?_⟩⟩
    rw [e, hdec _ _ _ hb hi, h, mul_zero]
  obtain ⟨π, hπS, hmin⟩ := Finset.exists_min_image S (permWt t) hSne
  obtain ⟨w, hw, hφw⟩ := (Finset.mem_filter.1 hπS).2
  obtain ⟨hsB, hsd⟩ := conj_diag (w := w) htD hw
  set x := chiDeltaU q α (w * t * w⁻¹) * φ w with hx
  have hx0 : x ≠ 0 := mul_ne_zero (chiDeltaU_ne_zero hq hα _) hφw
  have hterm : ∀ r ∈ R, φ (w * r * t) = if φ (w * r * t) = x then x else 0 := fun r hr => by
    split_ifs with h
    · exact h
    obtain ⟨b, w', i, π', hb, hw', hi, e⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv (w * r * t)
    rcases GlobalTheory.T.bruhat_weight_decreases L σ n t w w' b r i π π' htD htS hw hw' hb (hRI r hr) hi e with hlt | ⟨rfl, hord⟩
    · have hz : φ w' = 0 := by
        by_contra hz
        exact absurd (hmin π' (Finset.mem_filter.2 ⟨Finset.mem_univ _, w', hw', hz⟩)) (not_le.2 hlt)
      rw [e, hdec _ _ _ hb hi, hz, mul_zero]
    · exfalso
      apply h
      rw [e, hdec _ _ _ hb hi, isPermW_unique hw' hw, hx,
        chiDeltaU_congr q α (b' := w * t * w⁻¹) fun a => by rw [hord, hsd]]
  have h1 : φ (w * 1 * t) = x := by
    have e : w * 1 * t = (w * t * w⁻¹) * w := by group
    rw [e, hB _ _ hsB]
  have hsum := congrFun h0 w
  simp only [aOp, Pi.zero_apply] at hsum
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : (R.filter fun r => φ (w * r * t) = x).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨h1R, h1⟩)
  exact (mul_ne_zero (Nat.cast_ne_zero.2 hc) hx0) hsum

def iwFix (σ : L →+* L) (n : ℕ) (q : ℕ) (α : Fin (n / 2) → ℂˣ) : Submodule ℂ (GU σ n → ℂ) where
  carrier := {φ | φ ∈ psSpaceU σ q α ∧ ∀ g, ∀ i ∈ IwU σ n, φ (g * i) = φ g}
  add_mem' h h' := ⟨add_mem h.1 h'.1, fun g i hi => by simp [h.2 g i hi, h'.2 g i hi]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ _ => rfl⟩
  smul_mem' c _ h := ⟨Submodule.smul_mem _ c h.1, fun g i hi => by simp [h.2 g i hi]⟩

theorem finiteDimensional_iwFix (hσ : ∀ x, σ (σ x) = x) (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (q : ℕ)
    (α : Fin (n / 2) → ℂˣ) : FiniteDimensional ℂ (iwFix σ n q α) := by
  classical
  let wOf : Equiv.Perm (Fin n) → GU σ n := fun π => if h : ∃ w : GU σ n, IsPermW w π then h.choose else 1
  have hwOf : ∀ (w : GU σ n) π, IsPermW w π → wOf π = w := fun w π hw => by
    have h : ∃ w : GU σ n, IsPermW w π := ⟨w, hw⟩
    simp only [wOf, dif_pos h]
    exact isPermW_unique h.choose_spec hw
  let F : iwFix σ n q α →ₗ[ℂ] (Equiv.Perm (Fin n) → ℂ) :=
    { toFun := fun φ π => (φ : GU σ n → ℂ) (wOf π)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective F ?_
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨b, w, i, π, hb, hw, hi, rfl⟩ := GlobalTheory.T.unitary_iwasawa_bruhat_decomposition L σ n hσ hσv g
  have h1 : (φ : GU σ n → ℂ) w = 0 := by
    have := congrFun hφ π
    rwa [show F φ π = (φ : GU σ n → ℂ) (wOf π) from rfl, hwOf w π hw] at this
  have h2 := φ.2.2 (b * w) i hi
  have h3 := φ.2.1 b w hb
  show (φ : GU σ n → ℂ) (b * w * i) = 0
  rw [h2, h3, h1, mul_zero]

end U

theorem satPowNonvan : PositivityTheory.SphericalProduct.SatPowNonvan := by
  intro L _ _ _ ϖ σ q n hU α t htD htS j₀
  have hσ := hU.1
  have hσv := hU.2.1
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hα : ∀ i, (fun i => (α i : ℂ)) i ≠ 0 := fun i => (α i).ne_zero
  obtain ⟨hKI, hYI⟩ := GlobalTheory.T.unitary_iwahori_index_finite L ϖ σ q n hU
  obtain ⟨R, h1R, hRP, hR⟩ := GlobalTheory.T.coset_reps_of_factorization (GU σ n) (IwU σ n) t (fun u => u ∈ IwU σ n ∧ IsUnipU u)
    ⟨one_mem _, isBorelU_one, fun i => by simp⟩ (hYI t) (fun i hi => by
      obtain ⟨u, hu, hu', y, hy, hy', e⟩ := GlobalTheory.T.unitary_iwahori_factorization L σ n hσ hσv t htD htS i hi
      exact ⟨u, hu, ⟨hu, hu'⟩, y, hy, hy', e⟩)
  have hRI : ∀ r ∈ R, r ∈ IwU σ n := fun r hr => (hRP r hr).1
  have hRt : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ KU σ n := fun r hr k =>
    GlobalTheory.T.dominant_conjugate_unipotent_mem L σ n t r htD htS (hRP r hr).1 (hRP r hr).2.2 k
  obtain ⟨φ₀, hsph, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ)) hα
  have hIK := GlobalTheory.CompanionTheory.KUFactsU.iwU_le_KU σ n
  have hK : ∀ g, ∀ k ∈ KU σ n, φ₀ (g * k) = φ₀ g := fun g k hk => by
    simpa [chiDeltaU_one] using hsph 1 g k isBorelU_one hk
  have hφ₀ : φ₀ ∈ iwFix σ n q α :=
    ⟨fun b g hb => by simpa using hsph b g 1 hb (one_mem _), fun g i hi => hK g i (hIK hi)⟩
  haveI := finiteDimensional_iwFix hσ hσv q α
  exact abs_main (KU σ n) (IwU σ n) hIK hKI t R h1R hRI hRt hR (iwFix σ n q α)
    (fun φ hφ => ⟨fun b g hb => by
        show aOp R t φ (b * g) = _ * aOp R t φ g
        simp only [aOp, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_assoc b, mul_assoc b, hφ.1 b _ hb], aOp_rightInv _ t R hRI hR φ hφ.2⟩)
    (fun φ hφ h0 => aOp_inj q hq _ hα hσ hσv t htD htS R h1R hRI φ hφ.1 hφ.2 h0)
    φ₀ hφ₀ hK h1 (fun j => SatU ϖ q (dosetInd ℂ (KU σ n) (t ^ j)) (fun i => (α i : ℂ)))
    (fun j => by
      have e := Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _ hα
        (dosetInd ℂ (KU σ n) (t ^ j)) (Final.DosetIndMem _ (KU σ n) ℂ _) φ₀ hsph
      have := congrFun e 1
      simpa [h1] using this) j₀

end GlobalTheory.CompanionTheory.SatPow

end
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satake_power_nonvanishing : PositivityTheory.SphericalProduct.SatPowNonvan := by
  atlas_forward_decl GlobalTheory.CompanionTheory.SatPow.satPowNonvan
end
