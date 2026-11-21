import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrism
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrismMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.FirstFace
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.STrans
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.PiRepApply
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSStein
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CJoin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.RedApplyMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CTriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CLatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CMu
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsOfInLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.BlkEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CGtNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.GtEqZeta
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaDiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBetaVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.InLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.TorsStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.PhiZSeq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCountAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.BockAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.FibCount
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSDetect
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardKerEqCoker
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.KerFDelNm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.EqHomLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.DatEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CountOrdP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TorsionExponentBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActUPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelLCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardEQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInvLe
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSFewOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.RingEquivalences.OrderOfOneAddPrimePowZmodPrimePow
import Development.EtaleCohomology.CyclotomicDiscriminants.FinSLayer
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.NumThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.CardAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.PrimeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.NumFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalU

section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

noncomputable section

namespace UpperTheory.V.ZK.Coc

variable {A K : Type} [CommRing A] [CommGroup K]

private def F (u : K → K → A) (v : K → A) : (n : ℕ) → (Fin n → K) → A
  | 0, _ => 1
  | 1, g => v (g 0)
  | n + 2, g => u (g 0) (g 1) * F u v n fun i => g i.succ.succ

private theorem F_coc (u : K → K → A) (v : K → A) (hu : ∀ a b c, u b c - u (a * b) c + u a (b * c) - u a b = 0)
    (hv : ∀ a b, v (a * b) = v a + v b) : ∀ (n : ℕ) (g : Fin (n + 1) → K),
    F u v n (fun i => g i.succ) + ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) * F u v n (Fin.contractNth j (· * ·) g) = 0
  | 0, g => by simp [F]
  | 1, g => by
    simp [F, Fin.sum_univ_two, Fin.contractNth, hv]
  | n + 2, g => by
    have ih := F_coc u v hu hv n fun i => g i.succ.succ
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have h2 : ∀ j : Fin (n + 1), F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := fun j => by
      rw [F]
      congr 2
      funext i
      simp only [Fin.contractNth, Fin.val_succ, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]
      rfl
    have h0 : F u v (n + 2) (Fin.contractNth 0 (· * ·) g) = u (g 0 * g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h1 : F u v (n + 2) (Fin.contractNth (Fin.succ 0) (· * ·) g) =
        u (g 0) (g 1 * g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h3 : F u v (n + 2) (fun i => g i.succ) = u (g 1) (g 2) * F u v n fun i => g i.succ.succ.succ := by
      rw [F]; rfl
    have h4 : ∑ j : Fin (n + 1), (-1 : A) ^ ((j.succ.succ : ℕ) + 1) * F u v (n + 2) (Fin.contractNth j.succ.succ (· * ·) g) =
        u (g 0) (g 1) * ∑ j : Fin (n + 1), (-1 : A) ^ ((j : ℕ) + 1) *
          F u v n (Fin.contractNth j (· * ·) fun i => g i.succ.succ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2, Fin.val_succ, Fin.val_succ]; ring
    rw [h4, h0, h1, h3, eq_neg_of_add_eq_zero_right ih]
    simp only [Fin.val_zero, Fin.val_succ]
    linear_combination (F u v n fun i => g i.succ.succ.succ) * hu (g 0) (g 1) (g 2)

private theorem F_ins (u : K → K → A) (v : K → A) (hs : ∀ a b, u a b = u b a) (x : K) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    ∑ i : Fin (2 * E + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1) (Fin.insertNth (α := fun _ => K) i x g) =
      F u v (2 * E) g * v x
  | 0, g => by simp [F]
  | E + 1, g => by
    obtain ⟨a, g, rfl⟩ : ∃ (a : K) (g' : Fin (2 * E + 1) → K), g = (Fin.cons a g' : Fin (2 * E + 1 + 1) → K) := ⟨_, _, (Fin.cons_self_tail (n := 2 * E + 1) g).symm⟩
    obtain ⟨b, g, rfl⟩ : ∃ (b : K) (g' : Fin (2 * E) → K), g = (Fin.cons b g' : Fin (2 * E + 1) → K) := ⟨_, _, (Fin.cons_self_tail g).symm⟩
    change ∑ i : Fin (2 * E + 1 + 1 + 1), (-1 : A) ^ (i : ℕ) * F u v (2 * E + 1 + 2)
      (Fin.insertNth (α := fun _ => K) i x (Fin.cons a (Fin.cons b g : Fin (2 * E + 1) → K) : Fin (2 * E + 1 + 1) → K)) =
      (u a b * F u v (2 * E) g) * v x
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, mul_assoc (u a b), ← F_ins u v hs x E g, Finset.mul_sum]
    simp only [Fin.insertNth_succ_cons, Fin.insertNth_zero', F, Fin.cons_zero, Fin.cons_one, Fin.cons_succ, Fin.val_zero,
      Fin.val_succ, hs x a]
    rw [← add_assoc]
    refine (congrArg₂ (· + ·) (by ring : _ = (0 : A)) (Finset.sum_congr rfl fun j _ => by ring)).trans (zero_add _)

private theorem F_prod (u : K → K → A) (v : K → A) : ∀ (E : ℕ) (g : Fin (2 * E) → K),
    F u v (2 * E) g = ∏ s : Fin E, u (g ⟨2 * s, by omega⟩) (g ⟨2 * s + 1, by omega⟩)
  | 0, g => by simp [F]
  | E + 1, g => by
    rw [Fin.prod_univ_succ]
    exact congrArg (u _ _ * ·) (F_prod u v E fun i => g i.succ.succ)

private theorem ex_log [Finite K] [IsCyclic K] (q : ℕ) (ζ : K) (hζ : orderOf ζ = q) :
    ∃ (r : ℕ) (lg : K → ℤ), 0 < r ∧ (∀ a b, ((q * r : ℕ) : ℤ) ∣ lg a + lg b - lg (a * b)) ∧
      ∀ x : ℕ, ((q * r : ℕ) : ℤ) ∣ lg (ζ ^ x) - r * x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := K)
  choose y hy using hg
  simp only at hy
  have hN : 0 < orderOf g := orderOf_pos g
  have hd : ∀ m n : ℕ, g ^ m = g ^ n → (orderOf g : ℤ) ∣ (m : ℤ) - n := fun m n h =>
    (pow_eq_pow_iff_modEq.1 h).symm.dvd
  set r := (orderOf g).gcd (y ζ) with hr
  have hr0 : 0 < r := Nat.gcd_pos_of_pos_left _ hN
  have hq : q * r = orderOf g := by
    rw [← hζ, ← congrArg orderOf (hy ζ), orderOf_pow, hr, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]
  have hb := Nat.gcd_eq_gcd_ab (orderOf g) (y ζ)
  refine ⟨r, fun a => (orderOf g).gcdB (y ζ) * y a, hr0, fun a b => ?_, fun x => ?_⟩
  · rw [hq]
    have := hd (y a + y b) (y (a * b)) (by rw [pow_add, hy, hy, hy])
    push_cast at this
    simpa [mul_sub, mul_add] using this.mul_left ((orderOf g).gcdB (y ζ))
  · rw [hq]
    have := hd (y (ζ ^ x)) (y ζ * x) (by rw [pow_mul, hy, hy])
    push_cast at this
    have h2 := (this.mul_left ((orderOf g).gcdB (y ζ))).sub (dvd_mul_right (orderOf g : ℤ) ((orderOf g).gcdA (y ζ) * x))
    refine h2.trans (dvd_of_eq ?_)
    rw [hr, hb]; ring

end UpperTheory.V.ZK.Coc

open UpperTheory.V.ZK.Coc in
theorem UpperTheory.V.ZK.sCoc : UpperTheory.V.ZK.SCoc := by
  intro k _ _ q _ e ζ hζ v
  obtain ⟨r, lg, hr, h1, h2⟩ := ex_log q ζ hζ.eq_orderOf.symm
  have hN : ((q * r : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos (NeZero.pos q) hr).ne'
  choose U hU using h1
  have hs : ∀ a b, U a b = U b a := fun a b => mul_left_cancel₀ hN (by rw [← hU, ← hU, mul_comm a b]; ring)
  have hc : ∀ a b c, U b c - U (a * b) c + U a (b * c) - U a b = 0 := fun a b c =>
    mul_left_cancel₀ hN (by simp only [mul_sub, mul_add, ← hU, mul_assoc a b c]; ring)
  set u : kˣ → kˣ → ZMod q := fun a b => (U a b : ZMod q) with hu
  set w : kˣ → ZMod q := fun a => Multiplicative.toAdd (v a) with hw
  refine ⟨Finsupp.linearCombination _ (F u w _), ?_, fun x g => ?_⟩
  · rintro _ ⟨z, rfl⟩
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
    | single g c =>
      have := F_coc u w (fun a b c => by simp only [hu]; exact_mod_cast congrArg (Int.cast : ℤ → ZMod q) (hc a b c))
        (fun a b => by simp [hw]) _ g
      simp only [bd, Finsupp.linearCombination_single, map_smul, map_add, map_sum, one_smul, smul_eq_mul, one_mul]
      exact mul_eq_zero_of_right _ this
  · have key : ∑ j : ZMod q, u (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd j))
        (chi q ζ hζ.pow_eq_one x (Multiplicative.ofAdd 1)) = x := by
      set χ := chi q ζ hζ.pow_eq_one x with hχ
      have e1 : ((q * r : ℕ) : ℤ) * ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          q * lg (χ (Multiplicative.ofAdd 1)) := by
        simp only [Finset.mul_sum, ← hU, ← map_mul, ← ofAdd_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        have := Equiv.sum_comp (Equiv.addRight (1 : ZMod q)) fun j => lg (χ (Multiplicative.ofAdd j))
        simp only [Equiv.coe_addRight] at this
        rw [this]; simp
      obtain ⟨m, hm⟩ := h2 (x * (1 : ZMod q).val)
      have e2 : lg (χ (Multiplicative.ofAdd 1)) = r * ((x * (1 : ZMod q).val : ℕ) + q * m) := by
        have : χ (Multiplicative.ofAdd 1) = ζ ^ (x * (1 : ZMod q).val) := rfl
        rw [this]; push_cast at hm ⊢; linear_combination hm
      have e3 : ∑ j : ZMod q, U (χ (Multiplicative.ofAdd j)) (χ (Multiplicative.ofAdd 1)) =
          (x * (1 : ZMod q).val : ℕ) + q * m := mul_left_cancel₀ hN (by rw [e1, e2]; push_cast; ring)
      have := congrArg (Int.cast : ℤ → ZMod q) e3
      simpa [hu] using this
    have hp : ∀ h : Fin (2 * e + 1 + 1) → kˣ, Finsupp.linearCombination (ZMod q) (F u w _)
        (prism (ZMod q) g _ (Finsupp.single h 1)) = F u w (2 * (e + 1)) h * w g := fun h => by
      rw [← F_ins u w (fun a b => by simp only [hu, hs a b]) g (e + 1) h]
      simp only [prism, Finsupp.linearCombination_single, one_smul, map_sum, map_smul, smul_eq_mul, mul_one, one_mul,
        inv_mul_cancel_comm, ite_self]
      rfl
    simp only [zc, map_sum, cm, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hp, F_prod]
    rw [← Finset.sum_mul, ← key, ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine congrArg (· * w g) (Finset.sum_congr rfl fun j _ => Finset.prod_congr rfl fun s _ => ?_)
    have a1 : 2 * (s : ℕ) % 2 = 0 := by omega
    have a2 : ¬(2 * (s : ℕ) + 1) % 2 = 0 := by omega
    have a3 : 2 * (s : ℕ) / 2 = s := by omega
    simp only [a1, a2, a3, if_true, if_false, Fin.eta]

end
end

section
noncomputable section

namespace UpperTheory.V.ZK

private theorem gl_hom_transvection_eq_one_of_ne_zero_of_ne_one {k M : Type} [Field k] [CommGroup M] {n : ℕ} (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (Φ : GL (Fin n) k →* M) (t : Matrix.TransvectionStruct (Fin n) k) (u : GL (Fin n) k)
    (hu : (u : Matrix (Fin n) (Fin n) k) = t.toMatrix) : Φ u = 1 := by
  obtain ⟨i, j, hij, c⟩ := t
  change (u : Matrix (Fin n) (Fin n) k) = Matrix.transvection i j c at hu
  have hD : IsUnit (Matrix.diagonal (Function.update (fun _ => (1 : k)) i a)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro l _
    rw [Function.update_apply]
    split_ifs
    · exact ha0
    · exact one_ne_zero
  have hT : ∀ x : k, IsUnit (Matrix.transvection i j x).det := by
    intro x
    rw [Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one
  have hcomm : ∀ x : k, Matrix.diagonal (Function.update (fun _ => (1 : k)) i a) * Matrix.transvection i j x =
      Matrix.transvection i j (a * x) * Matrix.diagonal (Function.update (fun _ => (1 : k)) i a) := by
    intro x
    ext r s
    simp only [Matrix.transvection, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply, Function.update_apply]
    rcases eq_or_ne r i with rfl | hr <;> rcases eq_or_ne s j with rfl | hs
    · simp [hij, Ne.symm hij]
    · by_cases hrs : r = s
      · subst hrs
        simp [Ne.symm hs]
      · simp [hs, Ne.symm hs, hrs]
    · by_cases hrs : r = s
      · subst hrs
        simp [hr, Ne.symm hr]
      · simp [hr, Ne.symm hr, hrs]
    · by_cases hrs : r = s
      · subst hrs
        simp [hr, Ne.symm hr]
      · simp [hr, Ne.symm hr, hrs]
  let dU := Matrix.nonsingInvUnit _ hD
  let T : k → GL (Fin n) k := fun x => Matrix.nonsingInvUnit _ (hT x)
  have e1 : ∀ x, dU * T x = T (a * x) * dU := fun x => Units.ext (hcomm x)
  have e2 : ∀ x y, T x * T y = T (x + y) := fun x y =>
    Units.ext (Matrix.transvection_mul_transvection_same i j hij x y)
  have hu' : u = T c := Units.ext hu
  have ha : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hx : a * (c / (a - 1)) = c / (a - 1) + c := by
    field_simp
    ring
  have h3 := congrArg Φ (e1 (c / (a - 1)))
  rw [map_mul, map_mul, mul_comm (Φ dU), mul_left_inj, hx, ← e2, map_mul] at h3
  rw [hu']
  exact (mul_eq_left.mp h3.symm)

open Matrix in
private lemma gl_det {k M : Type} [Field k] [CommGroup M] {n : ℕ} (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (Φ : GL (Fin n) k →* M) (w : kˣ →* M)
    (hd : ∀ (g : GL (Fin n) k) (d : Fin n → kˣ), (g : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) →
      Φ g = ∏ i, w (d i)) (g : GL (Fin n) k) : Φ g = w (GeneralLinearGroup.det g) := by
  have key : ∀ A : Matrix (Fin n) (Fin n) k, A.det ≠ 0 →
      ∀ u : GL (Fin n) k, (u : Matrix (Fin n) (Fin n) k) = A → Φ u = w (GeneralLinearGroup.det u) := by
    intro A hA
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun A => ∀ u : GL (Fin n) k, (u : Matrix (Fin n) (Fin n) k) = A → Φ u = w (GeneralLinearGroup.det u))
      A hA ?_ ?_ ?_
    · intro D hD u hu
      rw [Matrix.det_diagonal] at hD
      have hD' : ∀ l, D l ≠ 0 := fun l => Finset.prod_ne_zero_iff.mp hD l (Finset.mem_univ l)
      have hdet : GeneralLinearGroup.det u = ∏ l, Units.mk0 (D l) (hD' l) := by
        ext
        rw [GeneralLinearGroup.val_det_apply, hu, Matrix.det_diagonal, Units.coe_prod]
        rfl
      rw [hd u (fun l => Units.mk0 (D l) (hD' l)) hu, hdet, map_prod]
    · intro t u hu
      rw [gl_hom_transvection_eq_one_of_ne_zero_of_ne_one a ha0 ha1 Φ t u hu]
      have h1 : GeneralLinearGroup.det u = 1 := by
        ext
        rw [GeneralLinearGroup.val_det_apply, hu, Matrix.TransvectionStruct.det]
        rfl
      rw [h1, map_one]
    · intro A B hA hB hPA hPB u hu
      have e : u = Matrix.nonsingInvUnit A (isUnit_iff_ne_zero.mpr hA) *
          Matrix.nonsingInvUnit B (isUnit_iff_ne_zero.mpr hB) := Units.ext hu
      rw [e, map_mul, map_mul, hPA _ rfl, hPB _ rfl, map_mul]
  refine key _ ?_ g rfl
  intro h
  have := (GeneralLinearGroup.det g).ne_zero
  rw [GeneralLinearGroup.val_det_apply] at this
  exact this h

private lemma fam_det {k M : Type} [Field k] [Finite k] [CommGroup M] (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (F : ∀ (V : Type) [AddCommGroup V] [Module k V] [Finite V], (V ≃ₗ[k] V) →* M) (w : kˣ →* M)
    (hiso : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W] [Module k W] [Finite W]
      (φ : V ≃ₗ[k] W) (g : V ≃ₗ[k] V), F W (cj φ g) = F V g)
    (hadd : ∀ (V W : Type) [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup W] [Module k W] [Finite W]
      (g : V ≃ₗ[k] V) (h : W ≃ₗ[k] W), F (V × W) (g.prodCongr h) = F V g * F W h)
    (hone : ∀ u : kˣ, F k (scal k u) = w u)
    (V : Type) [AddCommGroup V] [Module k V] [Finite V] (g : V ≃ₗ[k] V) : F V g = w (LinearEquiv.det g) := by
  classical
  have hdiag : ∀ (n : ℕ) (d : Fin n → kˣ),
      F (Fin n → k) (LinearEquiv.piCongrRight (fun i => scal k (d i))) = ∏ i, w (d i) := by
    intro n
    induction n with
    | zero =>
      intro d
      have h1 : (LinearEquiv.piCongrRight (fun i => scal k (d i)) : (Fin 0 → k) ≃ₗ[k] (Fin 0 → k)) = 1 := by
        ext x i
        exact i.elim0
      rw [h1, map_one, Fin.prod_univ_zero]
    | succ n ih =>
      intro d
      have hc := hiso (k × (Fin n → k)) (Fin (n + 1) → k) (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => k))
        ((scal k (d 0)).prodCongr (LinearEquiv.piCongrRight (fun i => scal k (d i.succ))))
      have he : cj (Fin.consLinearEquiv k (fun _ : Fin (n + 1) => k))
          ((scal k (d 0)).prodCongr (LinearEquiv.piCongrRight (fun i => scal k (d i.succ)))) =
          LinearEquiv.piCongrRight (fun i => scal k (d i)) := by
        ext x i
        refine Fin.cases ?_ ?_ i
        · simp [cj, scal]
        · intro j
          simp [cj, scal]
          rfl
      rw [he, hadd, hone, ih] at hc
      rw [Fin.prod_univ_succ]
      exact hc
  have hstd : ∀ (n : ℕ) (g₀ : (Fin n → k) ≃ₗ[k] (Fin n → k)), F (Fin n → k) g₀ = w (LinearEquiv.det g₀) := by
    intro n g₀
    let Φ : GL (Fin n) k →* M := (F (Fin n → k)).comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin n → k)).toMonoidHom.comp
        Matrix.GeneralLinearGroup.toLin.toMonoidHom)
    have hΦ : ∀ G : GL (Fin n) k, Φ G = F (Fin n → k)
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k _ (Matrix.GeneralLinearGroup.toLin G)) :=
      fun G => rfl
    have key := gl_det a ha0 ha1 Φ w (by
      intro G d hG
      rw [hΦ, ← hdiag n d]
      congr 1
      ext x i
      simp [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv, hG, Matrix.mulVec_diagonal, scal,
        Units.smul_def])
      (Matrix.GeneralLinearGroup.toLin.symm ((LinearMap.GeneralLinearGroup.generalLinearEquiv k _).symm g₀))
    rw [hΦ] at key
    simp only [MulEquiv.apply_symm_apply] at key
    rw [key]
    congr 1
    ext
    set G := Matrix.GeneralLinearGroup.toLin.symm
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (Fin n → k)).symm g₀) with hGdef
    have hG : LinearMap.GeneralLinearGroup.generalLinearEquiv k _ (Matrix.GeneralLinearGroup.toLin G) = g₀ := by
      simp [hGdef]
    rw [← hG, LinearEquiv.coe_det, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap,
      Matrix.GeneralLinearGroup.coe_toLin, Matrix.GeneralLinearGroup.val_det_apply]
    exact (LinearMap.det_toLin' _).symm
  haveI : Module.Finite k V := Module.Finite.of_finite
  have hc := hiso V _ (Module.finBasis k V).equivFun g
  rw [← hc, hstd]
  congr 1
  exact LinearEquiv.det_conj g (Module.finBasis k V).equivFun

private lemma conj_fix (h1 : SChain) {A : Type} [CommRing A] {C G : Type} [Group C] [Group G] (f : C →* G) (g : G)
    (hg : ∀ c, f c * g = g * f c) (m : ℕ) (z : Ch A C m) :
    cm A (MulAut.conj g⁻¹).toMonoidHom m (cm A f m z) = cm A f m z := by
  have h := (h1 A).2.2.1 C G G f (MulAut.conj g⁻¹).toMonoidHom m z
  rw [← h]
  congr 2
  ext c
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [mul_assoc, hg c, inv_mul_cancel_left]

private lemma cyc_cm (h1 : SChain) {A : Type} [CommRing A] {C G : Type} [Group C] [Group G] (f : C →* G)
    {m : ℕ} {z : Ch A C (m + 1)} (hz : Cyc z) : Cyc (cm A f (m + 1) z) := by
  unfold Cyc at *
  rw [(h1 A).2.1, hz, map_zero]

private lemma cyc_prism (h1 : SChain) (h2 : SPrism) {A : Type} [CommRing A] {C G : Type} [Group C] [Group G]
    (f : C →* G) (g : G) (hg : ∀ c, f c * g = g * f c) {m : ℕ} {z : Ch A C (m + 1)} (hz : Cyc z) :
    Cyc (prism A g (m + 1) (cm A f (m + 1) z)) := by
  have hw : Cyc (cm A f (m + 1) z) := cyc_cm h1 f hz
  have hp := h2 A G g m (cm A f (m + 1) z)
  unfold Cyc at hw ⊢
  rw [hw, map_zero, add_zero, conj_fix h1 f g hg (m + 1) z, sub_self] at hp
  exact hp

private lemma scal_comm {k V : Type} [Field k] [AddCommGroup V] [Module k V] (u : kˣ) (g : V ≃ₗ[k] V) :
    scal V u * g = g * scal V u := by
  ext x
  simp [scal, Units.smul_def]

theorem sThetaOf : SThetaOf := by
  intro h1 h2 h3 h4 h5 h6 k _ _ q _ e ζ hζ v
  obtain ⟨t, ht0, htv⟩ := h6 k q e ζ hζ v
  have hcard : ((Nat.card k : ℕ) : ZMod q) = 1 := by
    have hd : q ∣ Nat.card kˣ := by
      rw [hζ.eq_orderOf]
      exact orderOf_dvd_natCard ζ
    rw [Nat.card_units] at hd
    have hpos : 0 < Nat.card k := Nat.card_pos
    rw [← Nat.sub_add_cancel hpos, Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).2 hd,
      Nat.cast_one, zero_add]
  obtain ⟨θ, hθ, hθk⟩ := h5 k (ZMod q) hcard (2 * e + 1 + 1) t ht0
  refine ⟨θ, hθ, ?_⟩
  unfold HasVal
  intro V _ _ _ x g
  by_cases hq : q = 1
  · subst hq
    exact Subsingleton.elim _ _
  have hq1 : 1 < q := by
    have := NeZero.ne q
    omega
  have ha0 : (ζ : k) ≠ 0 := ζ.ne_zero
  have ha1 : (ζ : k) ≠ 1 := by
    intro h
    exact hζ.ne_one hq1 (Units.val_eq_one.mp h)
  let w : kˣ →* Multiplicative (ZMod q) := MonoidHom.mk'
    (fun u => Multiplicative.ofAdd ((x : ZMod q) ^ (e + 1) * Multiplicative.toAdd (v u)))
    (by
      intro a b
      simp only [map_mul, toAdd_mul, mul_add, ofAdd_add])
  have hP : ∀ (W : Type) [AddCommGroup W] [Module k W] (g' : W ≃ₗ[k] W),
      Cyc (prism (ZMod q) g' (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) := by
    intro W _ _ g'
    exact cyc_prism (A := ZMod q) (m := 2 * e + 1) (z := zc q e) h1 h2
      ((scal W).comp (chi q ζ hζ.pow_eq_one x)) g' (fun c => scal_comm (chi q ζ hζ.pow_eq_one x c) g') (h4 q e)
  have hmul : ∀ (W : Type) [AddCommGroup W] [Module k W] [Finite W] (g₁ g₂ : W ≃ₗ[k] W),
      θ W (prism (ZMod q) (g₁ * g₂) (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) =
      θ W (prism (ZMod q) g₁ (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) +
      θ W (prism (ZMod q) g₂ (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e))) := by
    intro W _ _ _ g₁ g₂
    have hz : Cyc (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e)) :=
      cyc_cm h1 _ (h4 q e)
    have hb := hθ.bdry W _ (h3 (ZMod q) (W ≃ₗ[k] W) g₁ g₂ (2 * e + 1) _ hz)
    rw [conj_fix h1 ((scal W).comp (chi q ζ hζ.pow_eq_one x)) g₁
      (fun c => scal_comm (chi q ζ hζ.pow_eq_one x c) g₁) (2 * e + 1 + 1) (zc q e), map_sub, map_sub,
      sub_eq_zero, sub_eq_iff_eq_add] at hb
    rw [hb, add_comm]
  let F : ∀ (W : Type) [AddCommGroup W] [Module k W] [Finite W], (W ≃ₗ[k] W) →* Multiplicative (ZMod q) :=
    fun W _ _ _ => MonoidHom.mk'
      (fun g₁ => Multiplicative.ofAdd (θ W (prism (ZMod q) g₁ (2 * e + 1 + 1)
        (cm (ZMod q) ((scal W).comp (chi q ζ hζ.pow_eq_one x)) (2 * e + 1 + 1) (zc q e)))))
      (fun g₁ g₂ => by simp only [hmul W g₁ g₂, ofAdd_add])
  have key := fam_det (ζ : k) ha0 ha1 F w ?_ ?_ ?_ V g
  · exact Multiplicative.ofAdd.injective key
  · intro V' W' _ _ _ _ _ _ φ g'
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    have hc : (cj φ).comp ((scal V').comp (chi q ζ hζ.pow_eq_one x)) =
        (scal W').comp (chi q ζ hζ.pow_eq_one x) := by
      ext u y
      simp [cj, scal, Units.smul_def]
    rw [← hθ.iso V' W' φ _ (hP V' g'), (h1 _).2.2.2.1, ← (h1 _).2.2.1, hc]
  · intro V' W' _ _ _ _ _ _ g₁ g₂
    let f : Cq q →* (V' ≃ₗ[k] V') × (W' ≃ₗ[k] W') :=
      MonoidHom.prod ((scal V').comp (chi q ζ hζ.pow_eq_one x)) ((scal W').comp (chi q ζ hζ.pow_eq_one x))
    have hy := cyc_prism h1 h2 f (g₁, g₂) (fun c => Prod.ext (scal_comm _ g₁) (scal_comm _ g₂)) (h4 q e)
    have ha := hθ.add _ V' W' (MonoidHom.fst _ _) (MonoidHom.snd _ _) _ hy
    rw [(h1 _).2.2.2.1, (h1 _).2.2.2.1, (h1 _).2.2.2.1, ← (h1 _).2.2.1, ← (h1 _).2.2.1,
      ← (h1 _).2.2.1] at ha
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [← ofAdd_add]
    congr 1
  · intro u
    have hy := cyc_prism h1 h2 (chi q ζ hζ.pow_eq_one x) u (fun c => mul_comm _ _) (h4 q e)
    have hu := hθk _ hy
    rw [htv x u, (h1 _).2.2.2.1, ← (h1 _).2.2.1] at hu
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    rw [hu]

end UpperTheory.V.ZK

end
end

section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK
open Polynomial

private theorem exp_cong (w : ℕ) (g : ℤ[X]) : (X ^ w - 1 : ℤ[X]) ∣ expand ℤ (1 + w) g - g := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | monomial n a =>
    rw [expand_monomial, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, ← mul_sub]
    apply dvd_mul_of_dvd_right
    have h1 : (X : ℤ[X]) ^ (n * (1 + w)) - X ^ n = X ^ n * ((X ^ w) ^ n - 1 ^ n) := by
      ring
    rw [h1]
    exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow _ _ _) _

private theorem exp_step (w j : ℕ) (x : ℤ[X]) (hx : (X ^ w - 1 : ℤ[X]) ^ j ∣ x) :
    (X ^ w - 1 : ℤ[X]) ^ (j + 1) ∣ expand ℤ (1 + w) x - ((1 + w : ℕ) : ℤ[X]) ^ j * x := by
  obtain ⟨y, rfl⟩ := hx
  have hE : expand ℤ (1 + w) (X ^ w - 1 : ℤ[X]) = (X ^ w - 1) * ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i := by
    rw [mul_comm, geom_sum_mul]
    simp only [map_sub, map_pow, expand_X, map_one, ← pow_mul, mul_comm]
  have hSk : (X ^ w - 1 : ℤ[X]) ∣ ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i - ((1 + w : ℕ) : ℤ[X]) := by
    have h1 : ((1 + w : ℕ) : ℤ[X]) = ∑ i ∈ Finset.range (1 + w), ((1 : ℤ[X]) ^ i) := by simp
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow ((X : ℤ[X]) ^ w) 1 i
  have hSj := hSk.trans (sub_dvd_pow_sub_pow _ _ j)
  have key : expand ℤ (1 + w) ((X ^ w - 1 : ℤ[X]) ^ j * y) - ((1 + w : ℕ) : ℤ[X]) ^ j * ((X ^ w - 1) ^ j * y) =
      (X ^ w - 1) ^ j * ((( ∑ i ∈ Finset.range (1 + w), ((X : ℤ[X]) ^ w) ^ i) ^ j - ((1 + w : ℕ) : ℤ[X]) ^ j) *
        expand ℤ (1 + w) y + ((1 + w : ℕ) : ℤ[X]) ^ j * (expand ℤ (1 + w) y - y)) := by
    rw [map_mul, map_pow, hE, mul_pow]; ring
  rw [key, pow_succ]
  exact mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left hSj _) (dvd_mul_of_dvd_right (exp_cong w y) _))

private theorem exp_pow (k i : ℕ) : (((expand ℤ k).toLinearMap : Module.End ℤ ℤ[X]) ^ i) X = X ^ k ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Module.End.mul_apply, ih]; simp [← pow_mul, pow_succ']

private theorem exp_dvd (w M : ℕ) : (X ^ w - 1 : ℤ[X]) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
    (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i := by
  have hdeg : (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).natDegree = M := by
    rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hsum : ∑ i ∈ Finset.range (M + 1),
      (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i • (X : ℤ[X]) ^ (1 + w) ^ i =
      (aeval ((expand ℤ (1 + w)).toLinearMap : Module.End ℤ ℤ[X])
        (∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X])) X := by
    rw [aeval_eq_sum_range, hdeg, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, exp_pow]
  rw [hsum]
  clear hsum hdeg
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ_comm, map_mul, Module.End.mul_apply]
    have h := exp_step w n _ ih
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply,
      AlgHom.toLinearMap_apply]
    convert h using 3
    rw [zsmul_eq_mul]; push_cast; ring

private theorem nat_dvd (l c ν n : ℕ) (hl : l.Prime) (h0 : n ≠ 0) (hn : n < l ^ c) :
    (n : ZMod (l ^ ν)) ∣ (l : ZMod (l ^ ν)) ^ c := by
  obtain ⟨a, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  have hac : a ≤ c := by
    by_contra hca
    have h1 : l ^ c ≤ l ^ a := Nat.pow_le_pow_right hl.pos (by omega)
    have h2 : l ^ a ≤ l ^ a * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero l)))
    omega
  have hcop : Nat.Coprime u (l ^ ν) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hl).2 hu))
  refine ⟨(l : ZMod (l ^ ν)) ^ (c - a) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)), ?_⟩
  have hv : (u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) = 1 :=
    (ZMod.unitOfCoprime u hcop).mul_inv
  calc (l : ZMod (l ^ ν)) ^ c = (l : ZMod (l ^ ν)) ^ a * (l : ZMod (l ^ ν)) ^ (c - a) *
        ((u : ZMod (l ^ ν)) * (((ZMod.unitOfCoprime u hcop)⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν))) := by
        rw [hv, mul_one, ← pow_add, Nat.add_sub_cancel' hac]
    _ = _ := by push_cast; ring

private theorem diff_dvd (l c ν s t : ℕ) (hl : l.Prime) (h : s ≠ t) (hs : s < l ^ c) (ht : t < l ^ c) :
    ((s : ZMod (l ^ ν)) - t) ∣ (l : ZMod (l ^ ν)) ^ c := by
  rcases lt_or_gt_of_ne h with hst | hst
  · have h1 := nat_dvd l c ν (t - s) hl (by omega) (by omega)
    rw [Nat.cast_sub hst.le] at h1
    rw [← neg_sub, neg_dvd]
    exact h1
  · have h1 := nat_dvd l c ν (s - t) hl (by omega) (by omega)
    rwa [Nat.cast_sub hst.le] at h1

private theorem sgl_dvd {q : ℕ} [NeZero q] (a b : ZMod q) (h : a ∣ b) :
    (AddMonoidAlgebra.single a 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ∣ AddMonoidAlgebra.single b 1 - 1 := by
  obtain ⟨c, rfl⟩ := h
  have hc : a * c = c.val • a := by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  rw [hc]
  have h1 := sub_dvd_pow_sub_pow (AddMonoidAlgebra.single a (1 : ℤ)) 1 c.val
  rwa [one_pow, AddMonoidAlgebra.single_pow, one_pow] at h1

private theorem alg_dvd (q w M : ℕ) :
    (AddMonoidAlgebra.single (w : ZMod q) 1 - 1 : AddMonoidAlgebra ℤ (ZMod q)) ^ M ∣ ∑ i ∈ Finset.range (M + 1),
      AddMonoidAlgebra.single ((1 + (w : ZMod q)) ^ i)
        ((∏ j ∈ Finset.range M, (X - C ((1 + (w : ℤ)) ^ j)) : ℤ[X]).coeff i) := by
  have h := map_dvd (aeval (R := ℤ) (AddMonoidAlgebra.single (1 : ZMod q) (1 : ℤ))) (exp_dvd w M)
  simp only [map_sum, map_zsmul, map_pow, map_sub, map_one, aeval_X, AddMonoidAlgebra.single_pow, one_pow,
    nsmul_one, AddMonoidAlgebra.smul_single', mul_one, Nat.cast_pow, Nat.cast_add, Nat.cast_one] at h
  simpa only [map_pow] using h

private def push (q : ℕ) (t : ZMod q) : ZMod q × ZMod q →+ ZMod q where
  toFun x := x.1 + t * x.2
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add, Prod.snd_add]; ring

theorem UpperTheory.V.ZK.sEta :
    UpperTheory.V.ZK.SEta := by
  intro l c ν M hl hM _ t₀
  have hp : l.Prime := hl.out
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hF := alg_dvd (l ^ ν) (l ^ c) M
  simp only [Nat.cast_pow] at hF
  let φ : ZMod (l ^ ν) → AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν)) :=
    fun t => AddMonoidAlgebra.mapDomainRingHom ℤ (push (l ^ ν) t)
  have hφ : ∀ (t : ZMod (l ^ ν)) (η : AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν))),
      φ t η = AddMonoidAlgebra.mapDomain (fun x : ZMod (l ^ ν) × ZMod (l ^ ν) => x.1 + t * x.2) η := by
    intro t η
    simp only [φ, AddMonoidAlgebra.mapDomainRingHom_apply]
    rfl
  have hφs : ∀ (t : ZMod (l ^ ν)) (x : ZMod (l ^ ν) × ZMod (l ^ ν)),
      φ t (AddMonoidAlgebra.single x 1) = AddMonoidAlgebra.single (x.1 + t * x.2) 1 := by
    intro t x; rw [hφ, AddMonoidAlgebra.mapDomain_single]
  let ι : AddMonoidAlgebra ℤ (ZMod (l ^ ν)) →+* AddMonoidAlgebra ℤ (ZMod (l ^ ν) × ZMod (l ^ ν)) :=
    AddMonoidAlgebra.mapDomainRingHom ℤ (AddMonoidHom.inl (ZMod (l ^ ν)) (ZMod (l ^ ν)))
  have hφι : ∀ t y, φ t (ι y) = y := by
    intro t y
    refine AddMonoidAlgebra.induction_linear y (by simp) (fun a b ha hb => by rw [map_add, map_add, ha, hb])
      (fun m r => ?_)
    simp only [ι, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, hφ]
    simp
  set s : Finset (Fin (M + 1)) := Finset.univ.erase t₀ with hs
  have hdiv : ∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1) ∣
      (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) ^ M := by
    have hcard : s.card = M := by simp [hs, Finset.card_erase_of_mem]
    calc _ ∣ ∏ _t' ∈ s, (AddMonoidAlgebra.single ((l : ZMod (l ^ ν)) ^ c) (1 : ℤ) - 1) :=
          Finset.prod_dvd_prod_of_dvd _ _ fun t' ht' => sgl_dvd _ _ (diff_dvd l c ν t₀ t' hp
            (fun h => (Finset.ne_of_mem_erase ht') (Fin.ext h).symm)
            (by have := t₀.isLt; omega) (by have := t'.isLt; omega))
      _ = _ := by rw [Finset.prod_const, hcard]
  obtain ⟨Q, hQ⟩ := hdiv.trans hF
  refine ⟨((∏ t' ∈ s, (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
      AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
      ι (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q)).coeff, ?_, ?_⟩
  · intro t ht
    rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod]
    rw [Finset.prod_eq_zero (i := t) (by simp [hs, ht]) (by rw [map_sub, hφs, hφs]; simp), zero_mul,
      AddMonoidAlgebra.coeff_zero]
  · rw [← AddMonoidAlgebra.coeff_mapDomain, ← hφ, map_mul, map_prod, hφι]
    have hfac : ∀ t' : Fin (M + 1), φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1) =
        AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ) *
          (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) - ((t' : ℕ) : ZMod (l ^ ν))) 1 - 1) := by
      intro t'
      rw [map_sub, hφs, hφs, mul_sub, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.one_def,
        mul_one]
      simp
    have h1 : (∏ t' ∈ s, AddMonoidAlgebra.single ((t' : ℕ) : ZMod (l ^ ν)) (1 : ℤ)) *
        AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 = 1 := by
      rw [AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, add_neg_cancel,
        Finset.prod_const_one, mul_one, AddMonoidAlgebra.one_def]
    have hmain : (∏ t' ∈ s, φ ((t₀ : ℕ) : ZMod (l ^ ν))
        (AddMonoidAlgebra.single ((0 : ZMod (l ^ ν)), (1 : ZMod (l ^ ν))) (1 : ℤ) -
          AddMonoidAlgebra.single (((t' : ℕ) : ZMod (l ^ ν)), (0 : ZMod (l ^ ν))) 1)) *
        (AddMonoidAlgebra.single (-∑ t' ∈ s, ((t' : ℕ) : ZMod (l ^ ν))) 1 * Q) =
        (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
          ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q := by
      simp only [hfac, Finset.prod_mul_distrib]
      linear_combination (∏ t' ∈ s, (AddMonoidAlgebra.single (((t₀ : ℕ) : ZMod (l ^ ν)) -
        ((t' : ℕ) : ZMod (l ^ ν))) (1 : ℤ) - 1)) * Q * h1
    rw [hmain, ← hQ]
    simp [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single]
end

section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.sClassOf :
    UpperTheory.V.ZK.SClassOf :=
  cJoin cChain cFree cTriv cAct cSplit cSupp cLatLoc cMu cInt cVal cGtNe cGtEq cBetaDiv cBetaVal cRep cUnit
end

section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up

private theorem UpperTheory.V.ZK.rankCount_mod (hR : RankCount) (H B : Type) [AddCommGroup H] [inst : Module ℤ H]
    [AddCommGroup B] (q r : ℕ) (hq : 0 < q) (hB : ∀ b : B, q • b = 0) (hH : Finite (AddCommGroup.torsion H)) (X : Set H)
    (hX : Module.rank ℤ (Submodule.span ℤ X) ≤ r) (f : H →+ B) (S : Finset B)
    (hS : ∀ s ∈ S, ∃ x ∈ X, ∃ u : ℤ, s = f (SMul.smul (self := (AddCommGroup.toIntModule H).toSMul) u x)) :
    S.card ≤ q ^ r * Nat.card (AddCommGroup.torsion H) := by
  obtain rfl : inst = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  refine hR H B q r hq hB hH _ hX f S fun s hs => ?_
  obtain ⟨x, hx, u, e⟩ := hS s hs
  exact ⟨u • x, Submodule.smul_mem _ u (Submodule.subset_span hx), e⟩

private theorem UpperTheory.V.ZK.selmer_upper_bound_of_inputs (hS : TorsStab) (hD : Descend) (hZ : ZVal) (hR : RankCount) (hB : Bock)
    (hF : FibCount) : UpperTheory.V.ZK.SUpperOf := by
  intro hC hO L _ _ hL k hk hr l ν hl B _ _ Φ hΦ S hSm
  classical
  have hl0 : 0 < l := hl.out.pos
  have hq : 0 < l ^ ν := pow_pos hl0 ν
  have hqB : ∀ b : B, l ^ ν • b = 0 := fun b => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ ν)), ZMod.natCast_self, zero_smul]
  obtain ⟨φ, hφ, hφΦ⟩ := hD (𝓞 L) (l ^ ν) k B Φ hΦ
  choose! nn hnn using hSm
  obtain ⟨n, hn0, hnS⟩ : ∃ n, 2 * (k + 1) + 4 ≤ n ∧ ∀ s ∈ S, nn s ≤ n :=
    ⟨max (2 * (k + 1) + 4) (S.sup nn), le_max_left _ _, fun s hs => le_max_of_le_right (Finset.le_sup hs)⟩
  obtain ⟨β, hβ⟩ := hB (l ^ ν) hq (GL (Fin n) (𝓞 L)) k
  obtain ⟨hfin, hcard⟩ := hS L hL k (2 * (k + 1) + 4) n (by omega) hn0
  have hlev : ∀ t, n ≤ lev l n t := fun t => by
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (Nat.le_mul_of_pos_left _ hl0)
  obtain ⟨hfin', hcard'⟩ := hS L hL (k + 1) (2 * (k + 1) + 4) (lev l n k) le_rfl (hn0.trans (hlev k))
  obtain ⟨u, hu⟩ := hZ (𝓞 L) B (k + 1) l ν hl0 hqB φ hφ n k
  let g : LinearMap.ker (bd (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) k) →+ B :=
    (nsmulAddMonoidHom (l ^ k)).comp
      ((Φ n).toAddMonoidHom.comp (LinearMap.ker (bd (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) k)).subtype.toAddMonoidHom)
  have hg : ∀ y, g y = l ^ k • Φ n y.1 := fun y => rfl
  have key := hF _ _ B β g ((l ^ ν) ^ InfinitePlace.nrComplexPlaces L * tc L (2 * (k + 1) + 4) (k + 1)) ?_ S ?_
  · rw [hcard] at key
    exact key
  · intro T hT
    rw [← hcard']
    refine rankCount_mod hR _ B (l ^ ν) _ hq hqB hfin' _ (hO L hL k hk hr l hl0 n hn0) (φ (lev l n k)) T fun s hs => ?_
    obtain ⟨y, hy, rfl⟩ := hT s hs
    obtain ⟨z, hz, hzy⟩ := hβ y hy
    obtain ⟨x, hx⟩ := hφΦ n z hz
    refine ⟨zSeq (𝓞 L) hl0 x k, ⟨x, rfl⟩, u, ?_⟩
    rw [hg, ← hzy, ← hx, hu]
    rfl
  · intro s hs
    obtain ⟨y, hy, e⟩ := hnn s hs
    refine ⟨⟨cm _ (stab (𝓞 L) (nn s) n (hnS s hs)) (k + 1) y, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, (hC _).2.1, show bd _ _ k y = 0 from hy, map_zero]
    · rw [hg, hΦ.stab _ _ _ _ hy]
      exact e

theorem UpperTheory.V.ZK.sUpperOf :
    UpperTheory.V.ZK.SUpperOf :=
  selmer_upper_bound_of_inputs torsStab descend zVal rankCount bock fibCount
end

section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

theorem UpperTheory.V.ZK.sCount :
    UpperTheory.V.ZK.SCount := by
  intro L F _ _ _ _ _ hTC l c ν E b B _ ζ γ hL hE hF
  have hl : l.Prime := Fact.out
  obtain ⟨ha2, hfa, hfN⟩ := Ct.lte l c ν E hl hL.c_pos hL.c_two hL.c_le hE
  generalize (1 + l ^ c) ^ E = a at *
  obtain ⟨D, hD⟩ := Ct.datEx L F γ a ha2
  have hDa := hD.a_eq
  have hDn := hD.n_eq
  have hI := Ct.clFin L F γ a D hD
  obtain ⟨hEQf, hEQc⟩ := Ct.cardEQ L F γ a D hTC hL.gal hL.gen hD
  obtain ⟨hClf, hWf, hWc⟩ := Ct.cardW _ _ D hI hEQf
  obtain ⟨hEHf, hEHc⟩ := Ct.eqHomLe L F γ a l ν D hl hD hClf
  refine ⟨hEHf, ?_⟩
  have hlpow : l ^ (ν - c) ≠ 0 := (pow_pos hl.pos _).ne'
  have hbig : 2 ≤ a ^ l ^ (ν - c) := le_trans ha2 (Nat.le_self_pow hlpow a)
  have hN0 : a ^ l ^ (ν - c) - 1 ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = ordCompl[l] (a ^ l ^ (ν - c) - 1) := ⟨_, rfl⟩
  have hNm : a ^ l ^ (ν - c) - 1 = l ^ (ν + E.factorization l) * m := by
    have h0 := Nat.ordProj_mul_ordCompl_eq_self (a ^ l ^ (ν - c) - 1) l
    rw [← hm, hfN] at h0
    exact h0.symm
  have hmd : ¬ l ∣ m := by
    rw [hm]
    exact Nat.not_dvd_ordCompl hl hN0
  have hker : ((D.a : ℤ)) ^ D.n - 1 = ((l ^ ν : ℕ) : ℤ) * ((l ^ E.factorization l * m : ℕ) : ℤ) := by
    rw [hDa, hDn, hL.ord]
    have h1 : 1 ≤ a ^ l ^ (ν - c) := by omega
    have key : ((a ^ l ^ (ν - c) - 1 : ℕ) : ℤ) = (a : ℤ) ^ l ^ (ν - c) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [← key, hNm]
    push_cast
    ring
  obtain ⟨f, hfnm, hfk⟩ := Ct.kerF _ _ D (l ^ ν) (l ^ b) _ hker
  haveI := hWf
  haveI := hEQf
  haveI := hClf
  have hrange := Ct.fewLe L F γ a (l ^ b) (l ^ ν) B D hD hF f hfnm hWf
  obtain ⟨hSLf, hSLc⟩ := Ct.selLCard L l hl
  obtain ⟨hSIf, hSIc⟩ := Ct.selInvLe L F l c ν a ζ γ D hl hL hD hSLf
  have hdvd : (l : ℤ) ∣ (D.a : ℤ) - 1 := by
    rw [hDa]
    have hc1 := hL.c_pos
    have hd : l ∣ a - 1 := Nat.dvd_of_factorization_pos (by rw [hfa]; omega)
    have h1 : 1 ≤ a := by omega
    have hd' := Int.natCast_dvd_natCast.mpr hd
    rw [Nat.cast_sub h1] at hd'
    simpa using hd'
  have htor := Ct.selInj _ _ D l hdvd hl.pos hSIf
  have hg : Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ l ^ gens L := by
    refine htor.trans (hSIc.trans ((Nat.mul_le_mul_right _ hSLc).trans (le_of_eq ?_)))
    unfold gens
    rw [← pow_add]
  have hp := Ct.pCount D.W _ f l (b + E.factorization l) (gens L) (m : ℤ) hl
    (by exact_mod_cast hmd)
    (by
      intro w hw
      have h0 := hfk w hw
      convert h0 using 2
      push_cast
      ring) hg
  have hEQ0 : Nat.card D.EQ ≠ 0 := Nat.card_pos.ne'
  have hCl0 : Nat.card D.ClQ ≠ 0 := Nat.card_pos.ne'
  have hfW : (Nat.card D.W).factorization l =
      (Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l := by
    rw [hWc, Nat.factorization_mul hEQ0 hCl0, Finsupp.add_apply]
  have hfEQ : (Nat.card D.EQ).factorization l + (c + E.factorization l) =
      InfinitePlace.nrComplexPlaces L * (ν + E.factorization l) := by
    have h0 := congrArg (fun n => n.factorization l) hEQc
    have ha1 : a - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul hEQ0 ha1, Finsupp.add_apply, hfa, hL.ord, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul, hfN] at h0
    exact h0
  calc Nat.card ↑(EqHom γ a (l ^ ν)) * (l ^ ν) ^ InfinitePlace.nrComplexPlaces L
      ≤ l ^ (Nat.card D.ClQ).factorization l *
          l ^ ((Nat.card D.EQ).factorization l + (c + E.factorization l)) := by
        refine Nat.mul_le_mul hEHc ?_
        rw [← pow_mul]
        refine Nat.pow_le_pow_right hl.pos ?_
        rw [hfEQ, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ = l ^ ((Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l) *
          l ^ (c + E.factorization l) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ (Nat.card ↥f.range * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [← hfW]
        exact hp
    _ ≤ (B * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrange)
    _ = B * l ^ ((b + E.factorization l) * gens L + c + E.factorization l) := by
        rw [mul_assoc, ← pow_add, add_assoc]
end

section
namespace UpperTheory.V.ZK.TorsionExponentBound

theorem exponent_le (e n N m D : ℝ) (he : 1 ≤ e) (hn : 1 ≤ n) (hN1 : 1 ≤ N) (hN : N ≤ 4 * e + 6)
    (hm : m ≤ 2 * e + 1) (hD : 1 ≤ D) :
    12 * (m + 1) * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + (m + 1) * (2 * (n * N * N)) + 2 * m ≤
      (2 * e * n) ^ 24 * Real.log (2 * D) := by
  have hD2 : (0 : ℝ) < 2 * D := by linarith
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL2 : Real.log 2 ≤ Real.log (2 * D) := Real.log_le_log (by norm_num) (by linarith)
  have hL : (0.69 : ℝ) < Real.log (2 * D) := by linarith
  have ha1 : 1 ≤ e * n := by nlinarith
  have hea : e ≤ e * n := by nlinarith
  have hP1 : 1 ≤ n * N := by nlinarith
  have hP : n * N ≤ 10 * (e * n) := by nlinarith
  have hNa : N ≤ 10 * (e * n) := by linarith
  have hm1 : m + 1 ≤ 4 * (e * n) := by linarith
  have hlogP : Real.log (2 * D * (n * N)) ≤ 16 * (e * n) * Real.log (2 * D) := by
    rw [Real.log_mul (ne_of_gt hD2) (ne_of_gt (by linarith))]
    have := Real.log_le_sub_one_of_pos (show 0 < n * N by linarith)
    nlinarith [mul_nonneg (sub_nonneg.2 hL.le) (by linarith : (0 : ℝ) ≤ 16 * (e * n) - 1)]
  have hlogP0 : 0 ≤ Real.log (2 * D * (n * N)) := Real.log_nonneg (by nlinarith)
  have hA0 : 0 ≤ 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) := by
    have : 0 ≤ n * N := by linarith
    positivity
  have hA : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N) ≤
      1920300 * (e * n) ^ 5 * Real.log (2 * D) := by
    have h3 : (n * N) ^ 3 ≤ (10 * (e * n)) ^ 3 := pow_le_pow_left₀ (by linarith) hP 3
    have t1 : 12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) ≤
        12 * (10 * (e * n)) ^ 3 * (10 * (e * n)) * (16 * (e * n) * Real.log (2 * D)) := by
      have : 0 ≤ (n * N) ^ 3 := by positivity
      have : 0 ≤ N := by linarith
      gcongr
    have t2 : 2 * (n * N * N) ≤ 300 * (e * n) ^ 5 * Real.log (2 * D) := by
      have q1 : n * N * N ≤ 10 * (e * n) * (10 * (e * n)) := by
        apply mul_le_mul hP hNa (by linarith) (by linarith)
      have q2 : (e * n) ^ 2 ≤ (e * n) ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
      have q3 : 0 ≤ (e * n) ^ 5 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL.le q3]
    have q4 : 0 ≤ Real.log (2 * D) := by linarith
    nlinarith [t1, t2]
  have hE : (2 * e * n) ^ 24 = 2 ^ 24 * (e * n) ^ 24 := by ring
  have hp6 : (e * n) ^ 6 ≤ (e * n) ^ 24 := pow_le_pow_right₀ ha1 (by norm_num)
  have hp1 : e * n ≤ (e * n) ^ 6 := by
    calc e * n = (e * n) ^ 1 := (pow_one _).symm
      _ ≤ (e * n) ^ 6 := pow_le_pow_right₀ ha1 (by norm_num)
  have hLpos : 0 ≤ Real.log (2 * D) := by linarith
  have k1 : (m + 1) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) ≤
      4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) := by
    calc _ ≤ 4 * (e * n) * (12 * (n * N) ^ 3 * N * Real.log (2 * D * (n * N)) + 2 * (n * N * N)) :=
          mul_le_mul_of_nonneg_right hm1 hA0
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by linarith)
  have k2 : 2 * m ≤ 12 * (e * n) ^ 6 * Real.log (2 * D) := by
    nlinarith [mul_le_mul_of_nonneg_right hp1 hLpos]
  have k3 : (e * n) ^ 6 * Real.log (2 * D) ≤ (e * n) ^ 24 * Real.log (2 * D) :=
    mul_le_mul_of_nonneg_right hp6 hLpos
  rw [hE]
  have k4 : 4 * (e * n) * (1920300 * (e * n) ^ 5 * Real.log (2 * D)) =
      7681200 * ((e * n) ^ 6 * Real.log (2 * D)) := by ring
  nlinarith [k1, k2, k3, k4]

end UpperTheory.V.ZK.TorsionExponentBound

open NumberField UpperTheory.V

namespace UpperTheory.V.ZK

theorem torsAll : ∃ C : ℝ, ∀ (L) [Field L] [NumberField L], IsTotallyComplex L →
    ∀ e N m : ℕ, 1 ≤ e → 1 ≤ N → N ≤ 4 * e + 6 → m ≤ 2 * e + 1 →
      Finite (UpperTheory.V.K.torsHGL L N m) ∧
        Real.log (Nat.card (UpperTheory.V.K.torsHGL L N m)) ≤
          UpperTheory.V.kBound C e (Module.finrank ℚ L) (discr L).natAbs := by
  refine ⟨24, ?_⟩
  intro L _ _ hL e N m he hN1 hN hm
  haveI := hL
  have ht := UpperTheory.V.KT.tors_le L N m
  refine ⟨ht.1, ?_⟩
  have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
  have hD : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero L)
  have hdd : 1 ≤ Module.finrank ℚ L * N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hA := UpperTheory.V.KT.orbnum L N m hN1
  have hBn : 0 < 2 * (discr L).natAbs * (Module.finrank ℚ L * N) := by positivity
  have hB : (0 : ℝ) < ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) := by exact_mod_cast hBn
  have hAexp : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
      Real.exp (12 * ((m : ℝ) + 1) * ((Module.finrank ℚ L : ℝ) * N) ^ 3 * N *
        Real.log (2 * ((discr L).natAbs : ℝ) * ((Module.finrank ℚ L : ℝ) * N))) := by
    have h1 : ((UpperTheory.V.KT.orbBound L N m : ℕ) : ℝ) ≤
        ((2 * (discr L).natAbs * (Module.finrank ℚ L * N) : ℕ) : ℝ) ^
          (12 * (m + 1) * (Module.finrank ℚ L * N) ^ 3 * N) := by exact_mod_cast hA
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hB] at h1
    refine h1.trans (le_of_eq ?_)
    congr 1
    push_cast
    ring
  have hsexp : (((3 ^ (UpperTheory.V.KT.dd L N * N) : ℕ)) : ℝ) ≤
      Real.exp (2 * ((Module.finrank ℚ L : ℝ) * N * N)) := by
    have hl3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    push_cast
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    push_cast
    have : (0 : ℝ) ≤ (Module.finrank ℚ L : ℝ) * N * N := by positivity
    nlinarith
  have hs1 : 1 ≤ 3 ^ (UpperTheory.V.KT.dd L N * N) := Nat.one_le_pow _ _ (by norm_num)
  have key := ht.log_le_exp hs1 hAexp hsexp
  refine key.trans ?_
  unfold UpperTheory.V.kBound
  apply Real.exp_le_exp.2
  have hE := UpperTheory.V.ZK.TorsionExponentBound.exponent_le (e : ℝ) (Module.finrank ℚ L : ℝ) (N : ℝ) (m : ℝ)
    ((discr L).natAbs : ℝ) (by exact_mod_cast he) (by exact_mod_cast hn) (by exact_mod_cast hN1)
    (by exact_mod_cast hN) (by exact_mod_cast hm) (by exact_mod_cast hD)
  refine hE.trans (le_of_eq ?_)
  rw [show ((24 : ℝ)) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end UpperTheory.V.ZK

open NumberField UpperTheory.V in
theorem UpperTheory.V.ZK.sTors :
    UpperTheory.V.ZK.STors := by
  obtain ⟨C, h⟩ := UpperTheory.V.ZK.torsAll
  exact ⟨C, fun L _ _ hL E hE m hm => (h L hL E (4 * E + 6) m hE (by omega) le_rfl hm).2⟩
end

section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

private theorem sf_card (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M]
    (h : IsFiniteLength ℤ_[l] M) : ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  induction h with
  | @of_subsingleton M' _ _ _ =>
    refine ⟨0, Module.length_eq_zero, ?_⟩
    haveI := uniqueOfSubsingleton (0 : M')
    simp
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule ℤ_[l] (M ⧸ N)›
    rw [IsLocalRing.eq_maximalIdeal hm] at e
    have hq : Nat.card (M ⧸ N) = l := by
      rw [Nat.card_congr e.toEquiv]
      exact (Nat.card_congr PadicInt.residueField.toEquiv).trans (Nat.card_zmod l)
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      push_cast
      rfl
    · have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
      rw [h2]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [hq, hc, pow_succ, mul_comm]

open KStar.TotallyRealRoots in
private theorem sf_nu {l : ℕ} [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (h0 : U.index ≠ 0) {e : ℕ} (he : e ≠ 0) :
    nu l U e ≤ ((2 + padicValNat l U.index + padicValNat l e : ℕ) : ℕ∞) := by
  have hp : Prime (l : ℤ_[l]) := PadicInt.prime_p
  have hunit : IsUnit (1 + (l : ℤ_[l]) ^ 2) := by
    rw [PadicInt.isUnit_iff]
    have h1 : ‖((l : ℤ_[l]) ^ 2)‖ < 1 := by
      rw [norm_pow, PadicInt.norm_p]
      have h2 : (1:ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      have h3 : (0:ℝ) < (l:ℝ)⁻¹ := by positivity
      have h4 : (l:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [PadicInt.norm_add_eq_max_of_ne] <;> simp_all [ne_of_gt, le_of_lt]
  have hmem : hunit.unit ^ U.index ∈ U := U.pow_index_mem hunit.unit
  by_contra hcon
  push_neg at hcon
  have hle : (((2 + padicValNat l U.index + padicValNat l e + 1 : ℕ)) : ℕ∞) ≤ nu l U e := by
    have := Order.add_one_le_of_lt hcon
    exact_mod_cast this
  have hdvd := (KStar.TotallyRealRoots.le_nu_iff.1 hle) _ hmem
  have hw : ((hunit.unit ^ U.index : ℤ_[l]ˣ) : ℤ_[l]) ^ e = (1 + (l:ℤ_[l]) ^ 2) ^ (U.index * e) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, pow_mul]
  rw [hw] at hdvd
  have hm := KStar.TotallyRealRoots.emultiplicity_pow_sub_one_sq (l := l) (u := 1 + (l:ℤ_[l]) ^ 2) (by simp) (U.index * e)
  rw [add_sub_cancel_left, emultiplicity_pow_self hp.ne_zero hp.not_unit,
    ← padicValNat_eq_emultiplicity (Nat.mul_ne_zero h0 he), padicValNat.mul h0 he] at hm
  have h5 := (pow_dvd_iff_le_emultiplicity).1 hdvd
  rw [hm] at h5
  norm_cast at h5
  omega

private theorem sf_loc {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (D : LData L Ω l) {e : ℕ} (he : e ≠ 0) :
    sumLocalH0TwistLength D e ≤ ((Module.finrank ℚ L * (2 + Nat.log l (Module.finrank ℚ L) + e) : ℕ) : ℕ∞) := by
  rw [LDataCardLeFinrank.local_H0_length_eq_sum]
  set n := Module.finrank ℚ L with hn
  have hv : ∀ v : D.S, KStar.TotallyRealRoots.nu l (LDataCardLeFinrank.decImage L l (D.A v)) ((e : ℤ).natAbs) ≤
      ((2 + Nat.log l n + e : ℕ) : ℕ∞) := by
    intro v
    obtain ⟨_, hi0, hin⟩ := LDataCardLeFinrank.ineOpen L Ω l v (D.A v) (LDataCardLeFinrank.above_of_mem D v) (D.hA v)
    have hdvd : (LDataCardLeFinrank.decImage L l (D.A v)).index ∣ (LDataCardLeFinrank.ineImage L l (D.A v)).index :=
      Subgroup.index_dvd_of_le (LDataCardLeFinrank.ineImage_le_decImage L l (D.A v))
    have hd0 : (LDataCardLeFinrank.decImage L l (D.A v)).index ≠ 0 := by
      intro h
      rw [h] at hdvd
      exact hi0 (Nat.eq_zero_of_zero_dvd hdvd)
    have hdn : (LDataCardLeFinrank.decImage L l (D.A v)).index ≤ n :=
      le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hdvd) hin
    have hne : (e : ℤ).natAbs ≠ 0 := by simpa using he
    refine le_trans (sf_nu _ hd0 hne) ?_
    have a1 : padicValNat l (LDataCardLeFinrank.decImage L l (D.A v)).index ≤ Nat.log l n :=
      le_trans (padicValNat_le_nat_log _) (Nat.log_mono_right hdn)
    have a2 : padicValNat l e ≤ e := by
      have hp := (Fact.out : l.Prime)
      have b1 : l ^ padicValNat l e ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) pow_padicValNat_dvd
      have b2 : padicValNat l e < l ^ padicValNat l e := Nat.lt_pow_self hp.one_lt
      omega
    have hea : (e : ℤ).natAbs = e := rfl
    rw [hea]
    exact_mod_cast (by omega : 2 + padicValNat l (LDataCardLeFinrank.decImage L l (D.A v)).index + padicValNat l e ≤
      2 + Nat.log l n + e)
  calc _ ≤ ∑ _v : D.S, ((2 + Nat.log l n + e : ℕ) : ℕ∞) := Finset.sum_le_sum fun v _ => hv v
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, ← Nat.cast_mul]
      exact_mod_cast Nat.mul_le_mul_right _ (LDataCardLeFinrank.cardAbove L Ω l D)

theorem UpperTheory.V.ZK.sFinal :
    UpperTheory.V.ZK.SFinal := by
  rw [SFinal.eq_1]
  rintro hPT hLF hLTD ⟨C, hC⟩
  obtain ⟨CK, _, hCK⟩ := K.numFin C
  refine ⟨CK, ?_⟩
  rw [LemmaK.eq_1]
  intro l _ L Ω _ _ _ _ _ D htc hmu e he
  rw [ShaK.eq_1] at hC
  obtain ⟨s, hs, hslog⟩ := hC l L htc hmu e he
  set n := Module.finrank ℚ L with hn
  have hV := LDataCardLeFinrank.VLen_le_shaLen_add hPT hLF hLTD (LDataCardLeFinrank.ptCase_of_isTotallyComplex L l) D (e : ℤ)
  rw [VLen.eq_1, LDataCardLeFinrank.shaLen_eq_shaInv, hs] at hV
  have hloc := sf_loc D (e := e) (by omega)
  have hlen : Module.length ℤ_[l] (H2 (zlTw D ((e : ℤ) + 1))) ≤ ((s + n * (2 + Nat.log l n + e) : ℕ) : ℕ∞) := by
    rw [Nat.cast_add]
    rw [← hn] at hloc
    exact le_trans hV (add_le_add le_rfl hloc)
  have hfl : IsFiniteLength ℤ_[l] (H2 (zlTw D ((e : ℤ) + 1))) := by
    rw [← Module.length_ne_top_iff]
    exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hlen
  obtain ⟨k, hk, hcard⟩ := sf_card l _ hfl
  have hkK : k ≤ s + n * (2 + Nat.log l n + e) := by
    rw [hk] at hlen
    exact_mod_cast hlen
  have hfin : Finite (H2 (zlTw D ((e : ℤ) + 1))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  refine ⟨hfin, ?_⟩
  rw [hcard, Nat.cast_pow, Real.log_pow]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1.le
  have hn1 : 1 ≤ n := Module.finrank_pos
  have hD1 : 1 ≤ (discr L).natAbs := Int.natAbs_pos.2 (discr_ne_zero L)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hDR : (1 : ℝ) ≤ (discr L).natAbs := by exact_mod_cast hD1
  have hln : (l : ℝ) ≤ n + 1 := by exact_mod_cast K.primeLe l L hmu
  have hX : Real.log l ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) hln
  have hX0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLog : (Nat.log l n : ℝ) * Real.log l ≤ Real.log ((n : ℝ) + 1) := by
    rw [← Real.log_pow]
    have hpl : ((l : ℝ) ^ Nat.log l n) ≤ n := by exact_mod_cast Nat.pow_log_le_self l (by omega)
    exact Real.log_le_log (by positivity) (by linarith)
  have hY : 1 / 2 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := by
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 2 ≤ Real.log (2 * ((discr L).natAbs : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hnum := hCK e n (discr L).natAbs he hn1 hD1
  have hk' : (k : ℝ) ≤ s + n * (2 + Nat.log l n + e) := by exact_mod_cast hkK
  have e1 : (k : ℝ) * Real.log l ≤ (s + n * (2 + Nat.log l n + e)) * Real.log l :=
    mul_le_mul_of_nonneg_right hk' hlogl
  have e2 : (n : ℝ) * (2 + e) * Real.log l ≤ n * (2 + e) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have e3 : (n : ℝ) * ((Nat.log l n : ℝ) * Real.log l) ≤ n * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hLog (by positivity)
  have hcoef : (3 + e : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ)) := by
    have q1 : (3 + e : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * (1 / 2) := by nlinarith
    have q2 : 4 * (2 * e * (2 * e + 3)) * (1 / 2 : ℝ) ≤ 4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ)) :=
      mul_le_mul_of_nonneg_left hY (by positivity)
    linarith
  have e4 : (n : ℝ) * (3 + e) * Real.log ((n : ℝ) + 1) ≤
      n * (4 * (2 * e * (2 * e + 3)) * Real.log (2 * ((discr L).natAbs : ℝ))) * Real.log ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity)) hX0
  linarith [e1, e2, e3, e4, hnum, hslog]
end

section
open Formalism.GaloisCohomology

namespace UpperTheory.V.ZK

theorem lemmaK (hB : BOdd) (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) :
    ∃ CK, LemmaK CK :=
  lemmaK_of_steps hB hP hF hT
    sChain sPrism sPrismMul sZc LateralTheory.Fin.SRel.intersectionNumber_baseChange sTrans sCoc sThetaOf sPhi sEta LateralTheory.Fin.SStein.intersectionNumber_baseChange sClassOf sUpperOf LateralTheory.Fin.SDetect.intersectionNumber_baseChange sCount LateralTheory.Fin.SFewOf.intersectionNumber_baseChange PositivityTheory.QuaternionShaBounds.sSha LateralTheory.Fin.SLayer.intersectionNumber_baseChange sTors sNum sFinal

end UpperTheory.V.ZK
end
