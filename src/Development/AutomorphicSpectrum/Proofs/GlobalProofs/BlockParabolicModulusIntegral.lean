import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearIntegralCompactOpenStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemConjSub
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldTopologyNormBalls
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex

open GlobalTheory.CompanionTheory.QL.NormalisedValue GlobalTheory.CompanionTheory.SplitRow.IdxV

section Line

variable {F : Type} [Field F]

def line (O : Subring F) (c : F) : AddSubgroup F :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft c)

theorem mem_line {O : Subring F} {c x : F} : x ∈ line O c ↔ ∃ o ∈ O, x = c * o := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩

theorem map_line (O : Subring F) (e c : F) :
    (line O c).map (AddMonoidHom.mulLeft e) = line O (e * c) := by
  ext x
  simp only [AddSubgroup.mem_map, mem_line, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    exact ⟨o, ho, by ring⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨c * o, ⟨o, ho, rfl⟩, by ring⟩

end Line

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem line_le_of_val_le (h : LF O ϖ nrm q) {x y : F} (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) : line O x ≤ line O y := by
  have hvy : 0 < ValuativeRel.valuation F y := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hy)
  have h1 : x / y ∈ O := by
    rw [mem_iff_val_le h, map_div₀]
    exact div_le_one_of_le₀ hxy zero_le'
  intro z hz
  obtain ⟨o, ho, rfl⟩ := mem_line.1 hz
  exact mem_line.2 ⟨x / y * o, O.mul_mem h1 ho, by field_simp⟩

theorem line_eq_of_val_eq (h : LF O ϖ nrm q) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ValuativeRel.valuation F x = ValuativeRel.valuation F y) : line O x = line O y :=
  le_antisymm (line_le_of_val_le h hy hxy.le) (line_le_of_val_le h hx hxy.ge)

theorem ball_eq_line (h : LF O ϖ nrm q) {d : F} (hd : d ≠ 0) : ball d = line O d⁻¹ := by
  ext x
  rw [mem_ball, mem_line, ← h.O_eq]
  constructor
  · intro hx
    exact ⟨_, hx, by field_simp⟩
  · rintro ⟨o, ho, rfl⟩
    rwa [mul_comm d⁻¹, mul_assoc, inv_mul_cancel₀ hd, mul_one]

theorem relIndex_line_pow (h : LF O ϖ nrm q) {c : F} (hc : c ≠ 0) (k : ℕ) :
    (line O (c * ϖ ^ k)).relIndex (line O c) = q ^ k := by
  have hϖ0 : ϖ ^ k ≠ 0 := pow_ne_zero _ h.ne
  have hp : ∃ p : 𝒪[F], Irreducible p ∧ (p : F) = (Units.mk0 ϖ h.ne : Fˣ) :=
    ⟨_, irreducible_pi h, rfl⟩
  have h1 := relIndex_ball (Units.mk0 ϖ h.ne) hp (k : ℤ)
  have hu : (((Units.mk0 ϖ h.ne : Fˣ) ^ (k : ℤ) : Fˣ) : F) = ϖ ^ k := by simp
  rw [hu, ball_eq_line h one_ne_zero, ball_eq_line h hϖ0, Int.toNat_natCast, inv_one] at h1
  have hinj : Function.Injective (AddMonoidHom.mulLeft (c * ϖ ^ k)) :=
    mul_right_injective₀ (mul_ne_zero hc hϖ0)
  have h2 := AddSubgroup.relIndex_map_map_of_injective (line O 1) (line O (ϖ ^ k)⁻¹) hinj
  rw [map_line, map_line, mul_one, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one] at h2
  rw [h2, h1, h.card]
  rfl

theorem relIndex_line (h : LF O ϖ nrm q) {c o : F} (hc : c ≠ 0) (ho : o ∈ O) (ho0 : o ≠ 0) :
    (((line O (c * o)).relIndex (line O c) : ℕ) : ℝ) = nrm c / nrm (c * o) := by
  obtain ⟨k, hk⟩ := val_eq_pow_of_int h ho0 ((mem_iff_val_le h o).1 ho)
  have hline : line O (c * o) = line O (c * ϖ ^ k) :=
    line_eq_of_val_eq h (mul_ne_zero hc ho0) (mul_ne_zero hc (pow_ne_zero _ h.ne))
      (by rw [map_mul, map_mul, hk, map_pow])
  have hq : (q : ℝ) ≠ 0 := by
    have := one_lt_q h
    exact_mod_cast (by omega : q ≠ 0)
  have hn : nrm o = ((q : ℝ) ^ k)⁻¹ := by
    have := nrm_eq_zpow h (x := o) (e := (k : ℤ)) (by simpa using hk)
    simpa [_root_.zpow_neg] using this
  have hnc : nrm c ≠ 0 := (nrm.pos hc).ne'
  rw [hline, relIndex_line_pow h hc k, map_mul, hn]
  push_cast
  field_simp

end Local

section Box

variable {F : Type} [Field F]

abbrev Idx {n : ℕ} (β : Fin n → ℕ) : Type := {p : Fin n × Fin n // β p.1 ≤ β p.2}

noncomputable def ext0 {n : ℕ} (β : Fin n → ℕ) : (Idx β → F) →+ Matrix (Fin n) (Fin n) F where
  toFun x := Matrix.of fun a b => if hab : β a ≤ β b then x ⟨(a, b), hab⟩ else 0
  map_zero' := by
    ext a b
    simp
  map_add' x y := by
    ext a b
    by_cases hab : β a ≤ β b <;> simp [hab]

theorem matrixExtendByZero_apply {n : ℕ} (β : Fin n → ℕ) (x : Idx β → F) (p : Idx β) :
    ext0 β x p.1.1 p.1.2 = x p := by
  have : β p.1.1 ≤ β p.1.2 := p.2
  simp [ext0, this]

theorem extendByZero_injective {n : ℕ} (β : Fin n → ℕ) : Function.Injective (ext0 (F := F) β) := by
  intro x y hxy
  funext p
  rw [← matrixExtendByZero_apply β x p, ← matrixExtendByZero_apply β y p, hxy]

theorem boxAdd_eq_map (O : Subring F) {n : ℕ} (β : Fin n → ℕ) (c : Fin n → Fin n → F) :
    boxAdd O β c =
      (AddSubgroup.pi Set.univ fun p : Idx β => line O (c p.1.1 p.1.2)).map (ext0 β) := by
  ext X
  constructor
  · rintro ⟨hX, hX'⟩
    refine AddSubgroup.mem_map.2 ⟨fun p => X p.1.1 p.1.2, ?_, ?_⟩
    · rw [AddSubgroup.mem_pi]
      intro p _
      exact mem_line.2 (hX' _ _)
    · ext a b
      by_cases hab : β a ≤ β b
      · simp [ext0, hab]
      · simp [ext0, hab, hX (not_le.1 hab)]
  · rintro h
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 h
    rw [AddSubgroup.mem_pi] at hx
    refine ⟨fun a b hab => ?_, fun a b => ?_⟩
    · simp [ext0, not_le.2 hab]
    · by_cases hab : β a ≤ β b
      · obtain ⟨o, ho, e⟩ := mem_line.1 (hx ⟨(a, b), hab⟩ (Set.mem_univ _))
        exact ⟨o, ho, by simpa [ext0, hab] using e⟩
      · exact ⟨0, O.zero_mem, by simp [ext0, hab]⟩

end Box

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (c c' : Fin n → Fin n → F), (∀ a b, c a b ≠ 0) → (∀ a b, c' a b ≠ 0) → (∀ a b, ∃ o ∈ O, c' a b = c a b * o) → (((boxAdd O β c').relIndex (boxAdd O β c) : ℕ) : ℝ) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => β p.1 ≤ β p.2), nrm (c p.1 p.2) / nrm (c' p.1 p.2) := by
  intro F _ _ _ _ O ϖ nrm q h n β c c' hc hc' hcc
  rw [boxAdd_eq_map, boxAdd_eq_map, AddSubgroup.relIndex_map_map_of_injective _ _ (extendByZero_injective β),
    relIndex_pi', Nat.cast_prod,
    Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => β p.1 ≤ β p.2)
      (p := fun p : Fin n × Fin n => β p.1 ≤ β p.2) (fun p => by simp)]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨o, ho, e⟩ := hcc p.1.1 p.1.2
  have ho0 : o ≠ 0 := by
    rintro rfl
    exact hc' p.1.1 p.1.2 (by simpa using e)
  rw [e]
  exact relIndex_line h (hc _ _) ho ho0

end GlobalTheory.CompanionTheory.QL.QIndex.BoxIndex
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.OnePlus

theorem nrm_det_one_add {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}
    (hLF : LF O ϖ nrm q) {n : ℕ} {x : Matrix (Fin n) (Fin n) F}
    (hx : ∀ a b, ∃ o ∈ O, x a b = ϖ * o) : nrm (1 + x).det = 1 := by
  obtain ⟨-, hϖ, hle, hlt, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  choose f hf hf' using hx
  let ϖ' : O := ⟨ϖ, hϖ⟩
  let y : Matrix (Fin n) (Fin n) O := fun a b => ⟨f a b, hf a b⟩
  let M : Matrix (Fin n) (Fin n) O := 1 + ϖ' • y
  have hM : O.subtype.mapMatrix M = 1 + x := by
    ext a b
    by_cases hab : a = b
    · simp [M, y, ϖ', hf', hab]
      rfl
    · simp [M, y, ϖ', hf', hab, Matrix.one_apply]
      rfl
  let π := Ideal.Quotient.mk (Ideal.span {ϖ'})
  have hπ : π ϖ' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hred : π.mapMatrix M = 1 := by
    simp only [M, map_add, map_one]
    have : π.mapMatrix (ϖ' • y) = 0 := by
      ext a b
      simp [hπ]
    rw [this, add_zero]
  have hdet : π M.det = 1 := by
    rw [RingHom.map_det, hred, Matrix.det_one]
  have hmem : M.det - 1 ∈ Ideal.span {ϖ'} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    exact sub_eq_zero.2 hdet
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hcoe : (1 + x).det = (M.det : F) := by
    rw [← hM, ← RingHom.map_det]
    rfl
  have hEq : (1 + x).det = 1 + (a : F) * ϖ := by
    have h2 := congrArg (Subtype.val) ha
    have h3 : (a : F) * ϖ = (M.det : F) - 1 := by simpa [ϖ'] using h2
    rw [hcoe, h3]
    ring
  have hin : (1 + x).det ∈ O := by
    rw [hcoe]
    exact M.det.2
  refine le_antisymm ((hle _).2 hin) (not_lt.1 fun hl => ?_)
  obtain ⟨o, ho, e⟩ := (hlt _).1 hl
  have h1 : (1 : F) = ϖ * (o - a) := by
    have : (1 : F) + (a : F) * ϖ = ϖ * o := by rw [← hEq, e]
    linear_combination this
  have h2 : nrm (1 : F) < 1 := (hlt 1).2 ⟨o - a, O.sub_mem ho a.2, h1⟩
  simp at h2

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ x : Matrix (Fin n) (Fin n) F, x ∈ boxAdd O β (fun _ _ => ϖ ^ T) ↔ ∃ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + x := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT x
  obtain ⟨-, hϖ, -, -, -, -, -⟩ := GlobalTheory.CompanionTheory.QL.NormalisedValue.main hLF
  constructor
  · rintro ⟨hbt, hent⟩
    have hx' : ∀ a b, ∃ o ∈ O, x a b = ϖ * o := fun a b => by
      obtain ⟨o, ho, e⟩ := hent a b
      have e' : x a b = ϖ ^ T * o := e
      have hTT : ϖ ^ T = ϖ * ϖ ^ (T - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hT]
      refine ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hϖ _) ho, ?_⟩
      rw [e', hTT, mul_assoc]
    have hdet := nrm_det_one_add hLF hx'
    have hne : (1 + x).det ≠ 0 := fun e => by
      rw [e] at hdet
      simp at hdet
    let g : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + x) hne
    have hg : (g : Matrix (Fin n) (Fin n) F) = 1 + x := rfl
    have hint : IsInt O (g : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [hg, Matrix.add_apply]
      obtain ⟨o, ho, e⟩ := hx' a b
      refine O.add_mem ?_ (e ▸ O.mul_mem hϖ ho)
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq]
        exact O.one_mem
      · rw [Matrix.one_apply_ne hab]
        exact O.zero_mem
    have hgQ : g ∈ Q := by
      rw [hQ, hg]
      intro i j hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hbt hij, hne']
    refine ⟨⟨g, hgQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨hint, hdet⟩, fun a b => ?_⟩
    obtain ⟨o, ho, e⟩ := hent a b
    refine ⟨o, ho, ?_⟩
    simpa [hg] using e
  · rintro ⟨p, hp, e⟩
    rw [Subgroup.mem_subgroupOf] at hp
    obtain ⟨-, hl⟩ := hp
    have hx : x = ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 := by
      rw [e]
      simp
    refine ⟨fun i j hij => ?_, fun a b => ?_⟩
    · have h0 := (hQ _).1 p.2 hij
      have hne' : i ≠ j := fun e => by
        subst e
        exact lt_irrefl _ hij
      simp [hx, h0, hne']
    · rw [hx]
      exact hl a b

end GlobalTheory.CompanionTheory.QL.QIndex.OnePlus
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe

section Field

variable {F : Type} [Field F]

theorem det_eq_one_add (O : Subring F) {c : F} (hc : c ∈ O) {n : ℕ}
    {g : Matrix (Fin n) (Fin n) F} (h : Lvl O c (g - 1)) : ∃ o ∈ O, g.det = 1 + c * o := by
  classical
  have hint : IsInt O g := fun i j => by
    obtain ⟨o, ho, e⟩ := h i j
    have e' : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨g i j, hint i j⟩
  have hM : O.subtype.mapMatrix M = g := by
    ext i j; rfl
  let c' : O := ⟨c, hc⟩
  let π := Ideal.Quotient.mk (Ideal.span {c'})
  have hc0 : π c' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c')
  have hπ : π.mapMatrix M = 1 := by
    ext i j
    obtain ⟨o, ho, e⟩ := h i j
    have e' : M i j = (1 : Matrix (Fin n) (Fin n) O) i j + c' * ⟨o, ho⟩ := by
      apply Subtype.ext
      have e2 : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
        rw [← e]; simp
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq] at e2 ⊢; simpa [M, c'] using e2
      · simpa [M, c', hij] using e2
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, e', map_add, map_mul, hc0, zero_mul, add_zero]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · simp [hij]
  have hdet : π (M.det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hπ, Matrix.det_one, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨a, a.2, ?_⟩
  have h1 : (O.subtype M.det) = g.det := by
    rw [RingHom.map_det, hM]
  have h2 : (a : F) * c = (M.det : F) - 1 := by
    simpa [c'] using congrArg Subtype.val ha
  have h3 : (M.det : F) = g.det := h1
  rw [← h3]
  linear_combination -h2

theorem diag_inv {n : ℕ} (g : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) :
    (∀ a, dd a ≠ 0) ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun a => (dd a)⁻¹ := by
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have hne : ∀ a, dd a ≠ 0 := fun a => by
    have h1 := congrFun (congrFun hmul a) a
    rw [hD, diagonal_mul, one_apply_eq] at h1
    exact left_ne_zero_of_mul_eq_one h1
  refine ⟨hne, ?_⟩
  have h2 : (diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hne a)
  calc ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = ((diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F)) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h2, Matrix.one_mul]
    _ = diagonal fun a => (dd a)⁻¹ := by rw [Matrix.mul_assoc, hmul, Matrix.mul_one]

theorem conj_entry {n : ℕ} (g p : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) (a b : Fin n) :
    (((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b =
      dd a * ((p : Matrix (Fin n) (Fin n) F) - 1) a b * (dd b)⁻¹ := by
  obtain ⟨-, hE⟩ := diag_inv g hD
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have h1 : ((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
      (g : Matrix (Fin n) (Fin n) F) * ((p : Matrix (Fin n) (Fin n) F) - 1) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hmul]
  rw [h1, hE, Matrix.mul_diagonal, hD, diagonal_mul]

end Field

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem mem_congGL_of_lvl (hLF : LF O ϖ nrm q) {n T : ℕ} (hT : 1 ≤ T) (g : GL (Fin n) F)
    (h : Lvl O (ϖ ^ T) ((g : Matrix (Fin n) (Fin n) F) - 1)) : g ∈ congGL O (ϖ ^ T) n := by
  obtain ⟨-, hpi, hle, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hc : ϖ ^ T ∈ O := O.pow_mem hpi T
  refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨fun i j => ?_, ?_⟩, h⟩
  · obtain ⟨o, ho, e⟩ := h i j
    have e' : (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j + ϖ ^ T * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  · obtain ⟨o, ho, e⟩ := det_eq_one_add O hc h
    rw [e]
    have hy : nrm (ϖ ^ T * o) < 1 := by
      refine (hlt _).2 ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hpi _) ho, ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    apply le_antisymm
    · refine (hult _ _).trans (max_le ?_ hy.le)
      simp
    · by_contra hcon
      have hcon' : nrm (1 + ϖ ^ T * o) < 1 := not_le.1 hcon
      have h1 := hult (1 + ϖ ^ T * o) (-(ϖ ^ T * o))
      rw [add_neg_cancel_right, map_one, map_neg_eq_map] at h1
      exact absurd h1 (not_le.2 (max_lt hcon' hy))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ d : Q, ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag → (∀ a b, ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b)⁻¹) ∈ O) → conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ≤ (congGL O (ϖ ^ T) n).subgroupOf Q ∧ ∀ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, (p ∈ conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ↔ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ boxAdd O β (lev ϖ T fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)) := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT d hdiag hd
  have hD : ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a :=
    hdiag.diagonal_diag.symm
  obtain ⟨hne, -⟩ := diag_inv (d : GL (Fin n) F) hD
  have hent := fun (p : GL (Fin n) F) => conj_entry (d : GL (Fin n) F) p hD
  have hconj : ∀ p : Q, ((d * p * d⁻¹ : Q) : GL (Fin n) F) =
      (d : GL (Fin n) F) * (p : GL (Fin n) F) * (d : GL (Fin n) F)⁻¹ := fun p => rfl
  have h2T : 1 ≤ 2 * T := by omega
  refine ⟨fun p hp => ?_, fun p _ => ?_⟩
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj] at hp
    rw [Subgroup.mem_subgroupOf]
    refine mem_congGL_of_lvl hLF hT _ fun a b => ?_
    obtain ⟨o, ho, e⟩ := hp.2 a b
    rw [hent] at e
    refine ⟨o * (ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b *
      (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)⁻¹)), O.mul_mem ho (hd b a), ?_⟩
    have hna := hne a
    have hnb := hne b
    field_simp at e ⊢
    linear_combination e
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj]
    constructor
    · intro hp
      refine ⟨((hQ _).1 p.2).sub (blockTriangular_one), fun a b => ?_⟩
      obtain ⟨o, ho, e⟩ := hp.2 a b
      rw [hent] at e
      refine ⟨o, ho, ?_⟩
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp at e ⊢
      linear_combination e
    · rintro ⟨-, hx⟩
      refine mem_congGL_of_lvl hLF h2T _ fun a b => ?_
      obtain ⟨o, ho, e⟩ := hx a b
      refine ⟨o, ho, ?_⟩
      rw [hent, e]
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp

end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
end

section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.ModB

variable {F : Type} [Field F]

def dg {n : ℕ} (v : Fin n → F) (hv : ∀ i, v i ≠ 0) : GL (Fin n) F where
  val := Matrix.diagonal v
  inv := Matrix.diagonal fun i => (v i)⁻¹
  val_inv := by simp [Matrix.diagonal_mul_diagonal, hv]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, hv]

end GlobalTheory.CompanionTheory.QL.ModB
end
