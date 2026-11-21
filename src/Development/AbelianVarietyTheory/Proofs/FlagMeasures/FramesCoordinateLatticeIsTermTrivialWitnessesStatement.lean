import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIntegralIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup

section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem cj_int (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map L.cj

theorem hf_sum_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) : hf L H (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L H (a i) y := by
  induction s using Finset.cons_induction with
  | empty => simp [hf]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hf_add_left, ih]

theorem hf_sum_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (a : ι → Fin n → E) (y : Fin n → E) : hf L H y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L H y (a i) := by
  induction s using Finset.cons_induction with
  | empty => simp [hf]
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, hf_add_right, ih]

theorem mem_perp_span (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (s : Set (Fin n → E))
    (x : Fin n → E) : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ s, hf L H x y = 0 := by
  have hmem : x ∈ perp L H (Submodule.span E s) ↔ ∀ y ∈ Submodule.span E s, hf L H x y = 0 := Iff.rfl
  rw [hmem]
  constructor
  · intro hx y hy
    exact hx y (Submodule.subset_span hy)
  · intro h y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => simp [hf]
    | add u v _ _ hu hv => rw [hf_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [hf_smul_right, hu, mul_zero]

section General
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_eq (g : Fin (r + 1) → S.V) :
    S.spanTo g r = Submodule.span E (Set.range fun j : Fin r => g j.castSucc) := by
  unfold Frames.spanTo
  congr 1
  ext v
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.isLt, rfl⟩

def proj (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) : S.V →ₗ[E] S.V where
  toFun v := v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j
  map_add' a b := by
    simp only [hf_add_left, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c a := by
    simp only [hf_smul_left, mul_smul, RingHom.id_apply, smul_sub, Finset.smul_sum]

theorem proj_apply (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (v : S.V) : proj S g gs v =
    v - ∑ j, hf L S.Hm v (gs j) • g j.castSucc - ∑ j, hf L S.Hm v (g j.castSucc) • gs j := rfl

def innerOf (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (Λ : Submodule L.O S.V) : Submodule L.O S.V :=
  (perp L S.Hm (S.spanTo g r)).restrictScalars L.O ⊓ Λ.comap ((proj S g gs).restrictScalars L.O)




end General

theorem mem_stdLat (L : LocE F E) {n : ℕ} (x : Fin n → E) : x ∈ stdLat L n ↔ ∀ i, x i ∈ L.O := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      show (Pi.single j 1 : Fin n → E) i ∈ L.O
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero => intro i; exact zero_mem _
    | add u v _ _ hu hv => intro i; exact add_mem (hu i) (hv i)
    | smul c u _ hu =>
      intro i
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
      exact mul_mem c.2 (hu i)
  · intro hx
    have hsum : x = ∑ i, (⟨x i, hx i⟩ : L.O) • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Subring.smul_def]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isSD_stdLat (L : LocE F E) {n : ℕ} (H K : Matrix (Fin n) (Fin n) E) (hH : IsIntM L H)
    (hK : IsIntM L K) (hKH : K * H = 1) : IsSD L H (stdLat L n) := by
  refine ⟨⟨Submodule.fg_span (Set.finite_range _), ?_⟩, ?_⟩
  · rw [eq_top_iff]
    intro v _
    have hsum : v = ∑ i, v i • (Pi.single i 1 : Fin n → E) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · intro y
    rw [mem_stdLat]
    constructor
    · intro h j
      have hrow : ∀ i, (Matrix.mulVec H fun k => L.cj (y k)) i ∈ L.O := by
        intro i
        have hs : (Pi.single i 1 : Fin n → E) ∈ stdLat L n := (mem_stdLat L _).2 fun k => by
          rw [Pi.single_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        have := h _ hs
        simpa [hf, Pi.single_apply, Matrix.mulVec, dotProduct] using this
      have hcK : (fun k => L.cj (y k)) = Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k)) := by
        rw [Matrix.mulVec_mulVec, hKH, Matrix.one_mulVec]
      have hcj : (Matrix.mulVec K (Matrix.mulVec H fun k => L.cj (y k))) j ∈ L.O := by
        simp only [Matrix.mulVec, dotProduct]
        exact Subring.sum_mem _ fun i _ => mul_mem (hK j i) (hrow i)
      rw [← hcK] at hcj
      have := cj_int L hcj
      simpa [L.cj_cj] using this
    · intro h x hx
      rw [mem_stdLat] at hx
      exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ =>
        mul_mem (mul_mem (hx i) (hH i j)) (cj_int L (h j))

section Blocks
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)

def extZ (x : Fin s → E) : Fin N → E := Sum.elim x 0 ∘ e.symm

def big (H : Matrix (Fin s) (Fin s) E) : Matrix (Fin N) (Fin N) E :=
  Matrix.reindex e e (Matrix.fromBlocks H 0 0 (1 : Matrix (Fin m) (Fin m) E))

theorem hf_extZ (L : LocE F E) (H : Matrix (Fin s) (Fin s) E) (x y : Fin s → E) :
    hf L (big e H) (extZ e x) (extZ e y) = hf L H x y := by
  have key : ∀ f : Fin N → E, ∑ i, f i = ∑ p, f (e p) := fun f => (e.sum_comp f).symm
  simp only [hf, key, Fintype.sum_sum_type, extZ, big, Matrix.reindex_apply, Matrix.submatrix_apply,
    Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    Matrix.fromBlocks_apply₁₁, zero_mul, map_zero, mul_zero, Finset.sum_const_zero, add_zero]

theorem big_mul (H K : Matrix (Fin s) (Fin s) E) (h : K * H = 1) : big e K * big e H = 1 := by
  simp [big, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, h,
    Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem big_herm (L : LocE F E) (H K : Matrix (Fin s) (Fin s) E) (hH : ∀ a b, L.cj (H b a) = H a b)
    (h : K * H = 1) : IsHermND L (big e H) := by
  refine ⟨?_, Matrix.isUnit_det_of_left_inverse (big_mul e H K h)⟩
  unfold IsHerm
  ext a b
  obtain ⟨p, rfl⟩ := e.surjective a
  obtain ⟨q, rfl⟩ := e.surjective b
  simp only [cT, big, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases q with q | q
  · simpa using hH p q
  · simp
  · simp
  · by_cases hpq : p = q
    · subst hpq
      simp
    · simp [Matrix.one_apply_ne hpq, Matrix.one_apply_ne (Ne.symm hpq)]

theorem big_int (L : LocE F E) (H : Matrix (Fin s) (Fin s) E) (hH : IsIntM L H) : IsIntM L (big e H) := by
  intro a b
  obtain ⟨p, rfl⟩ := e.surjective a
  obtain ⟨q, rfl⟩ := e.surjective b
  simp only [big, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases q with q | q
  · simpa using hH p q
  · simp
  · simp
  · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem extZ_mem (L : LocE F E) (x : Fin s → E) (hx : ∀ i, x i ∈ L.O) : extZ e x ∈ stdLat L N := by
  rw [mem_stdLat]
  intro i
  simp only [extZ, Function.comp_apply]
  rcases e.symm i with a | a
  · exact hx a
  · exact zero_mem _


end Blocks

def e4 (m : ℕ) : Fin 4 ⊕ Fin m ≃ Fin (m + 1 + 2 * 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def H4 : Matrix (Fin 4) (Fin 4) E := !![0,0,0,1; 0,-1,-1,0; 0,-1,0,0; 1,0,0,-1]

def K4 : Matrix (Fin 4) (Fin 4) E := !![1,0,0,1; 0,0,-1,0; 0,-1,1,0; 1,0,0,0]

theorem hermitian_four_inverse_mul : (K4 : Matrix (Fin 4) (Fin 4) E) * H4 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [K4, H4, Matrix.mul_apply, Fin.sum_univ_succ]

def toyExample (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) : Frames L 1 (m + 1) where
  ϖ := ϖ
  ϖ_irr := hϖ
  Hm := big (e4 m) H4
  herm := big_herm _ L _ K4 (by intro a b; fin_cases a <;> fin_cases b <;> simp [H4]) hermitian_four_inverse_mul
  T := 1
  T' := 1
  f := ![extZ (e4 m) ![1,0,0,0], extZ (e4 m) ![0,1,0,0]]
  f' := ![extZ (e4 m) ![0,0,1,0], extZ (e4 m) ![0,0,0,1]]
  es := ![extZ (e4 m) ![0,1,-1,1]]
  es' := ![extZ (e4 m) ![1,-1,0,1]]
  gram := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Fin.last]
  gram' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Fin.last]
  dual := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ]
  dual' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ]
  iso := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ]; simp [H4, hf, Fin.sum_univ_succ]
  iso' := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ]; simp [H4, hf, Fin.sum_univ_succ]
  w := ⟨[(1, 2)], rfl⟩
  relevant := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [hf_extZ] <;> simp [H4, hf, Fin.sum_univ_succ, Pt.mat, ptEntryL]
  G_ne := by
    haveI := nontrivial L
    simp [lead, Matrix.det_succ_row_zero, hf_extZ, Fin.sum_univ_succ, Fin.last, Fin.castLE, Fin.succAbove]
    simp [H4, hf, Fin.sum_univ_succ]
  gg := false
  gg_ok := by simp







def e6 (m : ℕ) : Fin 6 ⊕ Fin m ≃ Fin (m + 3 + 2 * 1 + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def H6 : Matrix (Fin 6) (Fin 6) E :=
  !![0,1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,1,0,0; 0,0,1,0,0,0; 0,0,0,0,-1,0; 0,0,0,0,0,1]

theorem hermitian_six_mul_self : (H6 : Matrix (Fin 6) (Fin 6) E) * H6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H6, Matrix.mul_apply, Fin.sum_univ_succ]

theorem hermitian_form_six_apply (L : LocE F E) (x y : Fin 6 → E) : hf L H6 x y =
    x 0 * L.cj (y 1) + x 1 * L.cj (y 0) + x 2 * L.cj (y 3) + x 3 * L.cj (y 2) - x 4 * L.cj (y 4) +
      x 5 * L.cj (y 5) := by
  simp [hf, Fin.sum_univ_succ, H6]
  ring

theorem isUnit_one_sub_sq (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : IsUnit (1 - ϖ ^ 2) := by
  have hv := Valuation.integer.integers (valuation F)
  have h1 : valuation F (ϖ : F) < 1 := by
    have hne : valuation F (algebraMap 𝒪[F] F ϖ) ≠ 1 := fun h =>
      hϖ.not_isUnit (hv.isUnit_iff_valuation_eq_one.2 h)
    exact lt_of_le_of_ne ((Valuation.mem_integer_iff _ _).1 ϖ.2) hne
  rw [hv.isUnit_iff_valuation_eq_one]
  have h2 : valuation F ((ϖ : F) ^ 2) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le h1 (by norm_num)
  have h3 : algebraMap 𝒪[F] F (1 - ϖ ^ 2) = 1 - (ϖ : F) ^ 2 := by
    rw [map_sub, map_one, map_pow]
    rfl
  rw [h3]
  exact Valuation.map_one_sub_of_lt _ h2

theorem coe_ne_zero (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) : (ϖ : F) ≠ 0 := by
  intro h
  exact hϖ.ne_zero (Subtype.ext h)

def toyG (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    Frames L 1 (m + 3) where
  ϖ := ϖ
  ϖ_irr := hϖ
  Hm := big (e6 m) H6
  herm := big_herm _ L _ H6 (by intro a b; fin_cases a <;> fin_cases b <;> simp [H6]) hermitian_six_mul_self
  T := 1
  T' := Units.map (𝒪[F]).subtype.toMonoidHom (isUnit_one_sub_sq ϖ hϖ).unit
  f := ![extZ (e6 m) ![1,0,0,0,0,0], extZ (e6 m) ![0,0,0,0,1,0]]
  f' := ![extZ (e6 m) ![1, -(algebraMap F E ϖ) ^ 2, algebraMap F E ϖ, algebraMap F E ϖ, 0, 0],
    extZ (e6 m) ![0,0,0,0,1,algebraMap F E ϖ]]
  es := ![extZ (e6 m) ![0,1,0,0,0,0]]
  es' := ![extZ (e6 m) ![0,1,0,0,0,0]]
  gram := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Fin.last]
  gram' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Fin.last] <;> ring
  dual := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply]
  dual' := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply]
  iso := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ, hermitian_form_six_apply]
  iso' := by
    intro a b; fin_cases a; fin_cases b; simp [hf_extZ, hermitian_form_six_apply]
  w := ⟨[(Units.map (algebraMap F E).toMonoidHom (Units.mk0 (ϖ : F) (coe_ne_zero ϖ hϖ)) ^ 2, 1), (-1, 1)], rfl⟩
  relevant := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [hf_extZ, hermitian_form_six_apply, Pt.mat, ptEntryL]
  G_ne := by
    haveI := nontrivial L
    have h6 : (algebraMap F E ϖ) ^ 6 ≠ 0 := by
      rw [← map_pow]
      exact (map_ne_zero _).2 (pow_ne_zero _ (coe_ne_zero ϖ hϖ))
    convert h6 using 1
    simp [lead, Matrix.det_succ_row_zero, hf_extZ, hermitian_form_six_apply, Fin.sum_univ_succ, Fin.last, Fin.castLE,
      Fin.succAbove]
    ring
  gg := true
  gg_ok := fun _ => ⟨hE, ⟨1, rfl⟩, ⟨(isUnit_one_sub_sq ϖ hϖ).unit, rfl⟩⟩








end GlobalTheory.HL.Inhab
end
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.CoordGood
open GlobalTheory.HL.Model GlobalTheory.HL.Inhab

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem adjugate_int (L : LocE F E) {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (h : IsIntM L A) :
    IsIntM L A.adjugate := by
  let B : Matrix (Fin n) (Fin n) L.O := fun i j => ⟨A i j, h i j⟩
  have hB : A = L.O.subtype.mapMatrix B := by ext i j; rfl
  rw [hB, ← RingHom.map_adjugate]
  intro i j
  exact (B.adjugate i j).2

theorem isSD_coordLat {L : LocE F E} {r k : ℕ} (S : Frames L r k) (h : Good S) :
    IsSD L S.Hm (coordLat S) := by
  obtain ⟨y, hy, hyd⟩ := h.Hm_unit
  refine isSD_stdLat L S.Hm (y • S.Hm.adjugate) h.Hm_int (fun i j => ?_) ?_
  · rw [Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hy (adjugate_int L _ h.Hm_int i j)
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm y, hyd, one_smul]

end

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hG
  haveI := nontrivial L
  have hsd := isSD_coordLat S hG
  have hmem : ∀ v : S.V, v ∈ coordLat S ↔ ∀ i, v i ∈ L.O := fun v => mem_stdLat L v
  have h1 : ∀ a, S.f a ∈ coordLat S := fun a => (hmem _).2 (hG.f_int a)
  have h2 : ∀ a, S.f' a ∈ coordLat S := fun a => (hmem _).2 (hG.f'_int a)
  have h3 : ∀ a, S.es a ∈ coordLat S := fun a => (hmem _).2 (hG.es_int a)
  have h4 : ∀ a, S.es' a ∈ coordLat S := fun a => (hmem _).2 (hG.es'_int a)
  have hint : ∀ x ∈ coordLat S, ∀ y ∈ coordLat S, hf L S.Hm x y ∈ L.O :=
    fun x hx y hy => (hsd.2 y).2 hy x hx
  have hZ : IsIntM L S.Zh := fun a b => hint _ (h2 b) _ (h1 a)
  have hU : IsUnit (S.D (Fin.last (r + 1))) := (GlobalTheory.FrameBasic.main L r k S).2.2.2.1
  obtain ⟨-, u, hu, hud⟩ := hG.D_unit _ hU.ne_zero
  have hDet : S.D (Fin.last (r + 1)) = S.Zh.det := rfl
  rw [hDet] at hud
  have e1 : S.Zh * (u • S.Zh.adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, mul_comm u, hud, one_smul]
  have e2 : (u • S.Zh.adjugate) * S.Zh = 1 := by
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, mul_comm u, hud, one_smul]
  generalize hPdef : u • S.Zh.adjugate = P at e1 e2
  have hP : IsIntM L P := fun i j => by
    rw [← hPdef, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hu (adjugate_int L _ hZ i j)
  haveI : IsNoetherianRing L.O := by
    obtain ⟨-, -, -, hpid, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
    infer_instance
  have hfg : (coordLat S).FG := hsd.1.1
  have hh := S.herm.1

  have hc : ∀ a, hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
      if a = Fin.last r then 1 else 0 := fun a => by
    have : hf L S.Hm (S.f a) (∑ b, P b (Fin.last r) • S.f' b) =
        L.cj ((S.Zh * P) a (Fin.last r)) := by
      rw [hf_sum_right, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hf_smul_right, map_mul, mul_comm, hf_symm L hh]
      rfl
    rw [this, e1, Matrix.one_apply]
    split_ifs <;> simp

  have hc' : ∀ b, hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
      if b = Fin.last r then 1 else 0 := fun b => by
    have : hf L S.Hm (S.f' b) (∑ a, L.cj (P (Fin.last r) a) • S.f a) =
        (P * S.Zh) (Fin.last r) b := by
      rw [hf_sum_right, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hf_smul_right, L.cj_cj]
      rfl
    rw [this, e2, Matrix.one_apply]
    simp [eq_comm]
  obtain ⟨A, hA, hA'⟩ := GlobalTheory.HL.FrameLift.core S S.f S.es S.T S.gram S.dual S.iso (coordLat S) hfg
    hsd.2 h1 h3 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun b => hP _ _) h2) hc
  obtain ⟨B, hB, hB'⟩ := GlobalTheory.HL.FrameLift.core S S.f' S.es' S.T' S.gram' S.dual' S.iso' (coordLat S)
    hfg hsd.2 h2 h4 _ (GlobalTheory.HL.FrameLift.sum_mem_O S _ _ (fun a => cj_int L (hP _ _)) h1) hc'
  refine ⟨(A, B, S.graphOf (coordLat S)), hA, hB, one_mem _, one_mem _, ?_, ?_, fun b => ?_, rfl⟩
  · rw [one_smul]; exact hA'
  · rw [one_smul]; exact hB'
  · refine ⟨S.f' b - S.f b, sub_mem (h2 b) (h1 b), ?_⟩
    simp [Frames.th, hG.gg]

end GlobalTheory.HL.CoordGood
end
end

section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framesCoordinateLattice_isTerm_trivialWitnesses : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → ∃ d₀, S.IsTermW d₀ (coordLat S) 1 1 := by
  first | exact @GlobalTheory.HL.CoordGood.main | exact GlobalTheory.HL.CoordGood.main | (intros; apply GlobalTheory.HL.CoordGood.main <;> assumption)
end
