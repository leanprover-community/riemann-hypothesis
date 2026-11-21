import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SmulPeriodMapMkZeroFstEqNegForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceEqFinrankMulSum
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn

section
noncomputable section

namespace GlobalTheory

namespace KerPerp

variable {O L Y : Type} [CommRing O] [StarRing O] [AddCommGroup L] [Module O L] [AddCommGroup Y] [Module O Y]
  {EF : LinearMap.BilinForm ℤ L} {y : L →ₗ[O] Y}

theorem exists_isotropic_section [Module.Projective O Y] {w : O} (hw : w + star w = 1) (halt : EF.IsAlt)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ s : Y →ₗ[O] L, (∀ x, y (s x) = x) ∧ ∀ x x', EF (s x) (s x') = 0 := by
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property y LinearMap.id hy
  have hs0' : ∀ x, y (s0 x) = x := fun x => LinearMap.congr_fun hs0 x
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : kerPerp hadj y ≤ LinearMap.ker y := fun t ht => hle t (mem_kerPerp.1 ht)
  obtain ⟨be, hbe_apply⟩ : ∃ be : LinearMap.BilinForm ℤ Y,
      ∀ x x', be x x' = EF (s0 x) (s0 (w • x')) :=
    ⟨EF.compl₁₂ s0.toAddMonoidHom.toIntLinearMap
      (s0.toAddMonoidHom.toIntLinearMap ∘ₗ (LinearMap.lsmul O Y w).toAddMonoidHom.toIntLinearMap),
      fun _ _ => rfl⟩
  have hbe : ∀ (a : O) x x', be (a • x) x' = be x (star a • x') := by
    intro a x x'
    rw [hbe_apply, hbe_apply, map_smul s0 a x, hadj, map_smul s0 w (star a • x'), map_smul s0 w x',
      map_smul s0 (star a) x', smul_comm]
  have hn := neg_apply_nilTo hadj hb hy hbe
  refine ⟨s0 + (kerPerp hadj y).subtype ∘ₗ nilTo hadj hb hy hbe ∘ₗ s0, fun x => ?_, fun x x' => ?_⟩
  · have h0 : y ((nilTo hadj hb hy hbe (s0 x) : L)) = 0 :=
      LinearMap.mem_ker.1 (hle' (nilTo hadj hb hy hbe (s0 x)).2)
    simp [hs0', h0]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add]
    have h1 := hn (s0 x) (s0 x')
    have h2 := hn (s0 x') (s0 x)
    rw [hs0', hs0', hbe_apply] at h1 h2
    have h3 := isotropic hle' (nilTo hadj hb hy hbe (s0 x)).2 (nilTo hadj hb hy hbe (s0 x')).2
    have h4 := skew (s0 x) (nilTo hadj hb hy hbe (s0 x'))
    have k1 : EF (s0 x') (s0 (w • x)) = -EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x, skew, hadj]
    have k2 : EF (s0 x) (s0 x') = EF (s0 x) (s0 (w • x')) + EF (s0 x) (star w • s0 x') := by
      rw [map_smul s0 w x', ← map_add (EF (s0 x)), ← add_smul, hw, one_smul]
    linarith

end KerPerp

theorem exists_split_of_coisotropic_ker (O L Y : Type) [CommRing O] [StarRing O] [AddCommGroup L] [Module O L]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [Module.Projective O Y] (w : O)
    (EF : LinearMap.BilinForm ℤ L) (y : L →ₗ[O] Y) (hw : w + star w = 1) (halt : ∀ x, EF x x = 0)
    (hb : Function.Bijective EF) (hadj : ∀ (a : O) x x', EF (a • x) x' = EF x (star a • x'))
    (hy : Function.Surjective y) (hle : ∀ t, (∀ v, y v = 0 → EF t v = 0) → y t = 0) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module O M) (EM : LinearMap.BilinForm ℤ M) (e : L ≃+ Y × (Y →+ ℤ) × M),
      Function.Bijective EM ∧ (∀ v, (e v).1 = y v) ∧
      (∀ (a : O) v x, (e (a • v)).2.1 x = (e v).2.1 (star a • x)) ∧
      (∀ (a : O) v, (e (a • v)).2.2 = a • (e v).2.2) ∧
      ∀ v v', EF v v' = (e v').2.1 (e v).1 - (e v).2.1 (e v').1 + EM (e v).2.2 (e v').2.2 := by
  obtain ⟨s, hsy, hsiso⟩ := KerPerp.exists_isotropic_section (EF := EF) (y := y) hw halt hb hadj hy hle
  have skew : ∀ a b, EF a b = -EF b a := by
    intro a b
    have h := halt (a + b)
    simp only [map_add, LinearMap.add_apply, halt a, halt b, zero_add, add_zero] at h
    linarith
  have hle' : KerPerp.kerPerp hadj y ≤ LinearMap.ker y := fun t ht =>
    hle t (KerPerp.mem_kerPerp.1 ht)
  obtain ⟨E, hE⟩ : ∃ E : KerPerp.kerPerp hadj y ≃ₗ[ℤ] Module.Dual ℤ Y,
      ∀ (t : KerPerp.kerPerp hadj y) (v : L), E t (y v) = -EF t v :=
    ⟨KerPerp.equivDual hadj hb hy, KerPerp.equivDual_apply hadj hb hy⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : L →ₗ[ℤ] Module.Dual ℤ Y, ∀ v x, Φ v x = -EF v (s x) :=
    ⟨-(EF.compl₂ s.toAddMonoidHom.toIntLinearMap), fun _ _ => rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : L →ₗ[ℤ] L, ∀ v, T v = ((E.symm (Φ v) : KerPerp.kerPerp hadj y) : L) :=
    ⟨(KerPerp.kerPerp hadj y).subtype.toAddMonoidHom.toIntLinearMap ∘ₗ E.symm.toLinearMap ∘ₗ Φ,
      fun _ => rfl⟩
  have hTK : ∀ v, T v ∈ KerPerp.kerPerp hadj y := fun v => by rw [hTdef]; exact (E.symm (Φ v)).2
  have hEF : ∀ (t : KerPerp.kerPerp hadj y) w, EF t w = -E t (y w) := fun t w => by rw [hE]; ring
  have hT : ∀ v w, EF (T v) w = EF v (s (y w)) := fun v w => by
    rw [hTdef, hEF, LinearEquiv.apply_symm_apply, hΦ, neg_neg]
  have hTy : ∀ v, y (T v) = 0 := fun v => LinearMap.mem_ker.1 (hle' (hTK v))
  obtain ⟨P, hP⟩ : ∃ P : L →ₗ[ℤ] L, ∀ v, P v = v - s (y v) - T v :=
    ⟨LinearMap.id - s.toAddMonoidHom.toIntLinearMap ∘ₗ y.toAddMonoidHom.toIntLinearMap - T,
      fun _ => rfl⟩
  have hPy : ∀ v, y (P v) = 0 := fun v => by
    rw [hP, map_sub, map_sub, hsy, hTy, sub_self, sub_zero]
  have hPs : ∀ v x, EF (P v) (s x) = 0 := fun v x => by
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hsiso, hT, hsy]
    ring
  obtain ⟨N, hN⟩ : ∃ N : Submodule O L, ∀ v, v ∈ N ↔ y v = 0 ∧ ∀ x, EF v (s x) = 0 :=
    ⟨{ carrier := {v | y v = 0 ∧ ∀ x, EF v (s x) = 0}
       add_mem' := fun {a b} ha hb => ⟨by rw [map_add, ha.1, hb.1, add_zero],
         fun x => by rw [map_add, LinearMap.add_apply, ha.2, hb.2, add_zero]⟩
       zero_mem' := ⟨map_zero y, fun x => by rw [map_zero, LinearMap.zero_apply]⟩
       smul_mem' := fun c v hv => ⟨by rw [map_smul, hv.1, smul_zero],
         fun x => by rw [hadj, ← map_smul s, hv.2]⟩ }, fun _ => Iff.rfl⟩
  have hPN : ∀ v, P v ∈ N := fun v => (hN _).2 ⟨hPy v, hPs v⟩
  have hΦN : ∀ m ∈ N, Φ m = 0 := fun m hm => LinearMap.ext fun x => by
    rw [hΦ, ((hN m).1 hm).2, neg_zero, LinearMap.zero_apply]
  have hPfix : ∀ m ∈ N, P m = m := fun m hm => by
    simp [hP, ((hN m).1 hm).1, hTdef, hΦN m hm]
  have hTsmul : ∀ (a : O) v, T (a • v) = a • T v := fun a v => hb.1 (LinearMap.ext fun w => by
    rw [hT, hadj, hadj, hT, map_smul y, map_smul s])
  have hdec : ∀ v, v = s (y v) + T v + P v := fun v => by rw [hP]; abel
  have hback : ∀ φ : Module.Dual ℤ Y, φ.toAddMonoidHom.toIntLinearMap = φ :=
    fun φ => LinearMap.ext fun _ => rfl
  let e : L ≃+ Y × (Y →+ ℤ) × N :=
    { toFun := fun v => (y v, (Φ v).toAddMonoidHom, ⟨P v, hPN v⟩)
      invFun := fun p => s p.1 + ((E.symm p.2.1.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
        (p.2.2 : L)
      left_inv := fun v => by
        show s (y v) + ((E.symm (Φ v).toAddMonoidHom.toIntLinearMap : KerPerp.kerPerp hadj y) : L) +
          P v = v
        rw [hback, ← hTdef]
        exact (hdec v).symm
      right_inv := fun p => by
        obtain ⟨a, φ, m⟩ := p
        have hyt : y ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) = 0 :=
          LinearMap.mem_ker.1 (hle' (E.symm _).2)
        have hym : y (m : L) = 0 := ((hN m).1 m.2).1
        have hyv : y (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) = a := by
          rw [map_add, map_add, hsy, hyt, hym, add_zero, add_zero]
        have hΦv : Φ (s a + ((E.symm φ.toIntLinearMap : KerPerp.kerPerp hadj y) : L) + m) =
            φ.toIntLinearMap := by
          refine LinearMap.ext fun x => ?_
          rw [hΦ, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hsiso, hEF, hsy,
            LinearEquiv.apply_symm_apply, ((hN m).1 m.2).2]
          simp
        refine Prod.ext hyv (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ _ x = φ x
          rw [hΦv]
          rfl
        · show P _ = m
          rw [hP, hyv, hTdef, hΦv]
          exact (fun p q r : L => show p + q + r - p - q = r by abel) _ _ _
      map_add' := fun a b => by
        refine Prod.ext (map_add y a b) (Prod.ext (AddMonoidHom.ext fun x => ?_) (Subtype.ext ?_))
        · show Φ (a + b) x = Φ a x + Φ b x
          rw [map_add, LinearMap.add_apply]
        · show P (a + b) = P a + P b
          exact map_add P a b }
  refine ⟨N, inferInstance, inferInstance,
    EF.compl₁₂ N.subtype.toAddMonoidHom.toIntLinearMap N.subtype.toAddMonoidHom.toIntLinearMap, e,
    ⟨?_, ?_⟩, fun v => rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply Subtype.ext
    apply hb.1
    refine LinearMap.ext fun w => ?_
    have hm' : EF (m : L) (P w) = 0 := by
      simpa using LinearMap.congr_fun hm ⟨P w, hPN w⟩
    have hmN := (hN m).1 m.2
    rw [Submodule.coe_zero, map_zero, LinearMap.zero_apply, hdec w, map_add, map_add, hmN.2, hm',
      skew, hT, hmN.1, map_zero, map_zero]
    simp
  · intro g
    obtain ⟨v, hv⟩ := hb.2 (g ∘ₗ (AddMonoidHom.mk' (fun v => (⟨P v, hPN v⟩ : N))
      (fun a b => Subtype.ext (map_add P a b))).toIntLinearMap)
    refine ⟨⟨P v, hPN v⟩, LinearMap.ext fun m => ?_⟩
    have h1 : EF v m = g ⟨P m, hPN m⟩ := LinearMap.congr_fun hv m
    have h2 : (⟨P m, hPN m⟩ : N) = m := Subtype.ext (hPfix m m.2)
    have hmN := (hN m).1 m.2
    show EF (P v) m = g m
    rw [hP]
    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2, skew (s (y v)), hmN.2, hT, hmN.1, map_zero, map_zero]
    simp
  · intro a v x
    show Φ (a • v) x = Φ v (star a • x)
    rw [hΦ, hΦ, hadj, map_smul s]
  · intro a v
    refine Subtype.ext ?_
    show P (a • v) = a • P v
    rw [hP, hP, map_smul y, map_smul s, hTsmul, smul_sub, smul_sub]
  · intro v v'
    show EF v v' = Φ v' (y v) - Φ v (y v') + EF (P v) (P v')
    rw [hΦ, hΦ, hP, hP]
    simp only [map_sub, LinearMap.sub_apply]
    have f1 := hT v v'
    have f2 := hT v (s (y v'))
    rw [hsy] at f2
    have f3 : EF v (T v') = -EF v' (s (y v)) := by rw [skew, hT]
    have f4 : EF (s (y v)) (T v') = -EF v' (s (y (s (y v)))) := by rw [skew, hT]
    rw [hsy] at f4
    have f5 := hsiso (y v) (y v')
    have f6 : EF (T v) (T v') = 0 := KerPerp.isotropic hle' (hTK v) (hTK v')
    have f7 := skew (s (y v)) v'
    linarith

end GlobalTheory
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexConjugate

namespace GlobalTheory.ComplementTypes

open NumberField in
open scoped ComplexConjugate in

theorem _root_.GlobalTheory.ComplementTypes.types (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p q r g g' : ℕ)
    (ty : Fin g → (E →+* ℂ)) (ty' : Fin g' → (E →+* ℂ)) (hty : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H p q ty)
    (h : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = (r : ℂ) * ∑ τ : E →+* ℂ, τ (H.bar a : E) + ∑ j, ty' j (a : E)) :
    r ≤ p ∧ r ≤ q ∧ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTypeFn H (p - r) (q - r) ty' := by
  classical
  let c : E →+* E := (IsCMField.complexConj E).toAlgHom.toRingHom
  have hcc : ∀ x, c (c x) = x := fun x => by simp [c]
  let t : (Fin r × (E →+* ℂ)) ⊕ Fin g' → (E →+* ℂ) := Sum.elim (fun k => k.2.comp c) ty'
  have hsum : ∀ a : 𝓞 E, ∑ i, ty i (a : E) = ∑ k, t k (a : E) := by
    intro a
    rw [h a, Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp [t, c, H.bar_eq]
  obtain ⟨e, he⟩ := _root_.GlobalTheory.PeriodNonempty.exists_equiv_of_sum_eq ty t hsum
  have key : ∀ τ : E →+* ℂ, Nat.card {i // ty i = τ} = r + Nat.card {j // ty' j = τ} := by
    intro τ
    have hc1 : ∀ σ : E →+* ℂ, σ.comp c = τ ↔ σ = τ.comp c := fun σ =>
      ⟨fun hσ => by ext x; rw [← hσ]; simp [hcc], fun hσ => by ext x; rw [hσ]; simp [hcc]⟩
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_congr (e.subtypeEquiv (p := fun i => ty i = τ) (q := fun k => t k = τ) fun i => by
        simp only [he]), Fintype.card_subtype,
      Fintype.card_subtype, Finset.card_filter, Finset.card_filter, Fintype.sum_sum_type,
      Fintype.sum_prod_type]
    simp only [t, Sum.elim_inl, Sum.elim_inr, hc1, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    congr 1
  have hd : (2 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.two_le
  have hconj : conj H.rt0 = -H.rt0 := by
    have hsq : conj H.rt0 ^ 2 = H.rt0 ^ 2 := by rw [← map_pow, H.sqrt_neg_disc_sq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h' | h'
    · exfalso
      have hre := Complex.conj_eq_iff_re.1 h'
      have h2 := H.sqrt_neg_disc_sq
      rw [← hre] at h2
      have h3 := congrArg Complex.re h2
      simp [pow_two] at h3
      nlinarith [mul_self_nonneg H.rt0.re]
    · exact h'
  have hne : -H.rt0 ≠ H.rt0 := by
    intro h0
    have h1 : H.rt0 = 0 := by linear_combination -h0 / 2
    have h2 := H.sqrt_neg_disc_sq
    rw [h1] at h2
    have h3 := congrArg Complex.re h2
    simp at h3
    have := H.d_prime.two_le
    omega
  have hroot : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    rw [← map_pow, h1, H.sqrt_neg_disc_sq]
    simp
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨τ1, h1⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨τ0, h0⟩
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj]⟩
  obtain ⟨τ2, h2⟩ : ∃ τ : E →+* ℂ, τ (H.rt : E) ≠ H.rt0 := by
    rcases hroot τ0 with h0 | h0
    · exact ⟨(starRingEnd ℂ).comp τ0, by simp [h0, hconj, hne]⟩
    · exact ⟨τ0, by rw [h0]; exact hne⟩
  have hp := (hty τ1).1 h1
  have hq := (hty τ2).2 h2
  have k1 := key τ1
  have k2 := key τ2
  refine ⟨by omega, by omega, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · have := (hty τ).1 hτ
    have := key τ
    omega
  · have := (hty τ).2 hτ
    have := key τ
    omega

end GlobalTheory.ComplementTypes
end

section
noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex

def sesq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (hermForm Hm)
    (fun _ _ _ => by simp [hermForm]) (fun _ _ _ => by simp [hermForm])
    (fun _ _ _ => by simp [hermForm, Matrix.mulVec_add]) (fun _ _ _ => by simp [hermForm, Matrix.mulVec_smul])

theorem sesq_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq Hm z w = hermForm Hm z w := rfl

theorem sesq_conj {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    starRingEnd ℂ (sesq Hm z w) = sesq Hm w z := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  simp only [sesq_apply, hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
    RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem sesq_of {n : ℕ} (S : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ) (z w : Fin n → ℂ) :
    hermForm (Matrix.of fun i j => S (Pi.single i 1) (Pi.single j 1)) z w = S z w := by
  conv_rhs => rw [pi_eq_sum_univ' z, pi_eq_sum_univ' w]
  simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

def imForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).im) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)

@[simp] theorem imForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : imForm S x y = (S x y).im := rfl

def reForm (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) : LinearMap.BilinForm ℝ W :=
  LinearMap.mk₂ ℝ (fun x y => (S x y).re) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r x]; simp) (fun _ _ _ => by simp)
    (fun r x y => by rw [← algebraMap_smul ℂ r y, LinearMap.map_smulₛₗ]; simp)

@[simp] theorem reForm_apply (S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x y : W) : reForm S x y = (S x y).re := rfl

theorem sesq_ext {ι : Type} {v : ι → W} (hv : Submodule.span ℝ (Set.range v) = ⊤) {S S' : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ}
    (h : ∀ i k, (S (v i) (v k)).im = (S' (v i) (v k)).im) (x y : W) : S x y = S' x y := by
  have h1 : imForm S = imForm S' := LinearMap.ext_on_range hv fun i => LinearMap.ext_on_range hv fun k => h i k
  have h2 : ∀ x y, (S x y).im = (S' x y).im := fun x y => congr($h1 x y)
  exact Complex.ext (by simpa using h2 (I • x) y) (h2 x y)

variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}

theorem exists_imPart [FiniteDimensional ℝ W] (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) :
    ∃ b : W →ₗ[ℝ] W, (∀ w, b w ∈ R) ∧ ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im := by
  have hnd : ((reForm S).restrict R).Nondegenerate := by
    constructor
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
    · intro x hx
      by_contra h
      exact (hpos x fun h0 => h (Subtype.ext h0)).ne' (hx x)
  refine ⟨R.subtype ∘ₗ (LinearMap.BilinForm.toDual _ hnd).symm.toLinearMap ∘ₗ (imForm S).domRestrict₂ R,
    fun w => Subtype.property _, fun w r hr => Complex.ext ?_ ?_⟩
  · exact LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) ((imForm S).domRestrict₂ R w) ⟨r, hr⟩
  · exact hR _ (Subtype.property _) r hr

section

variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)

omit [IsScalarTower ℝ ℂ W] in
include hpos hb hb' in

theorem imPart_eq {w c : W} (hc : c ∈ R) (h : ∀ r ∈ R, (S c r).re = (S w r).im) : b w = c := by
  by_contra hne
  have h1 := hpos _ (sub_ne_zero.2 hne)
  have h2 := R.sub_mem (hb w) hc
  rw [map_sub S, LinearMap.sub_apply, hb' w _ h2, Complex.sub_re, h _ h2] at h1
  simp at h1

omit [IsScalarTower ℝ ℂ W] in
include hconj hb' in

theorem apply_imPart (w : W) {r : W} (hr : r ∈ R) : S r (b w) = (S w r).im := by
  rw [← hconj, hb' w r hr, Complex.conj_ofReal]

variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)

omit [IsScalarTower ℝ ℂ W] in
include hpos hb hb' hρ hρR in

theorem imPart_act (a : O) (w : W) : b (ρ a w) = ρ a (b w) :=
  imPart_eq hpos hb hb' (hρR _ _ (hb w)) fun r hr => by
    rw [hρ, hρ, hb' _ _ (hρR _ _ hr), Complex.ofReal_re]

include hpos hb hb' hρ hρR in

theorem exists_compl [FiniteDimensional ℂ W] (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (n : ℕ) (q : W →ₗ[ℂ] (Fin n → ℂ)) (j : (Fin n → ℂ) →ₗ[ℂ] W) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧
      (∀ z, q (j z) = z) ∧ (∀ z, ∀ r ∈ R, S (j z) r = 0) ∧ (∀ w, w = b (I • w) + I • b w + j (q w)) ∧
      (∀ w, (∀ r ∈ R, S w r = 0) → j (q w) = w) ∧ ∀ a z, j (F a z) = ρ a (j z) := by
  let U : Submodule ℂ W :=
    { carrier := {u | ∀ r ∈ R, S u r = 0}
      zero_mem' := fun r _ => by simp
      add_mem' := fun {u u'} hu hu' r hr => by simp [hu r hr, hu' r hr]
      smul_mem' := fun c u hu r hr => by simp [hu r hr] }
  have hII : ∀ w : W, I • I • w = -w := fun w => by rw [smul_smul, I_mul_I, neg_smul, one_smul]
  have hsm : ∀ (c : ℂ) (w : W), c • w = c.re • w + c.im • I • w := fun c w => by
    rw [← algebraMap_smul ℂ c.re, ← algebraMap_smul ℂ c.im, smul_smul, ← add_smul]
    congr 1
    exact (re_add_im c).symm
  let p₀ : W →ₗ[ℝ] W := LinearMap.id - b ∘ₗ (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ -
    (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ ∘ₗ b
  have hp₀ : ∀ w, p₀ w = w - b (I • w) - I • b w := fun _ => rfl
  have hpI : ∀ w, p₀ (I • w) = I • p₀ w := fun w => by
    simp only [hp₀, hII, smul_sub, map_neg]; abel
  have hpU : ∀ w, p₀ w ∈ U := fun w r hr => by
    simp only [hp₀, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hb' _ r hr, smul_eq_mul]
    apply Complex.ext <;> simp
  let p : W →ₗ[ℂ] U :=
    { toFun := fun w => ⟨p₀ w, hpU w⟩
      map_add' := fun w w' => Subtype.ext (map_add p₀ w w')
      map_smul' := fun c w => Subtype.ext (by
        show p₀ (c • w) = c • p₀ w
        rw [hsm c w, hsm c (p₀ w), map_add, map_smul, map_smul, hpI]) }
  have hb0 : ∀ u ∈ U, b u = 0 := fun u hu => imPart_eq hpos hb hb' R.zero_mem fun r hr => by simp [hu r hr]
  have hpu : ∀ u : U, p u = u := fun u => Subtype.ext (by
    show p₀ u = u
    rw [hp₀, hb0 _ u.2, hb0 _ (U.smul_mem _ u.2), smul_zero, sub_zero, sub_zero])
  have hρU : ∀ a, ∀ u ∈ U, ρ a u ∈ U := fun a u hu r hr => by rw [hρ]; exact hu _ (hρR _ _ hr)
  let σ : O →+* Module.End ℂ U :=
    { toFun := fun a => (ρ a).restrict (hρU a)
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  obtain ⟨n, k, F, hF, hk⟩ := hQ U σ
  refine ⟨n, k.toLinearMap ∘ₗ p, U.subtype ∘ₗ k.symm.toLinearMap, F, hF, fun z => ?_, fun z => (k.symm z).2,
    fun w => ?_, fun w hw => ?_, fun a z => ?_⟩
  · simp [hpu]
  · have : (U.subtype ∘ₗ k.symm.toLinearMap) ((k.toLinearMap ∘ₗ p) w) = p₀ w := by simp [p]
    rw [this, hp₀]; abel
  · have := hpu ⟨w, hw⟩
    simp only at this
    simp [this]
  · obtain ⟨u, rfl⟩ := k.surjective z
    rw [← hk]
    simp [σ]

omit [IsScalarTower ℝ ℂ W] in
include hconj hR hb in

theorem sub_swap {w w' u u' : W} (hu : ∀ r ∈ R, S u r = 0) (hu' : ∀ r ∈ R, S u' r = 0)
    (h : w = b (I • w) + I • b w + u) (h' : w' = b (I • w') + I • b w' + u') :
    S w (b w') - S u u' / (2 * I) = S w' (b w) - S u' u / (2 * I) - (S w w').im := by
  have hv : ∀ r ∈ R, S r u' = 0 := fun r hr => by rw [← hconj, hu' r hr, map_zero]
  have hre : ∀ z z', (S z z').re = (S z' z).re := fun z z' => by rw [← hconj z z', conj_re]
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  generalize b (I • w) = a, hb (I • w) = ha at h
  generalize b (I • w') = a', hb (I • w') = ha' at h'
  generalize b w = c, hb w = hc at h ⊢
  generalize b w' = c', hb w' = hc' at h' ⊢
  subst h h'
  simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu _ ha', hu _ hc',
    hu' _ hc, hv _ ha, hv _ hc, AnArc.div_two_I]
  apply Complex.ext <;>
    simp [hR _ ha _ ha', hR _ ha _ hc', hR _ hc _ ha', hR _ hc _ hc', hR _ ha' _ hc, hR _ hc' _ hc, hre a' c, hre c' c,
      hre u' u, him u' u]
  ring

end

open NumberField in

theorem exists_diag {E : Type} [Field E] [NumberField E] (U : Type) [AddCommGroup U] [Module ℂ U]
    [FiniteDimensional ℂ U] (σ : 𝓞 E →+* Module.End ℂ U) :
    ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : 𝓞 E →+* Module.End ℂ (Fin n → ℂ)),
      (∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) ∧ ∀ a u, k (σ a u) = F a (k u) := by
  classical
  let T₀ : Set U := {v | ∃ φ : E →+* ℂ, ∀ a : 𝓞 E, σ a v = φ (a : E) • v}
  have hS : Submodule.span ℂ T₀ = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← EigenSplit.sum_proj (EigenSplit.isSplitting_complex E) σ v]
    refine Submodule.sum_mem _ fun φ _ => Submodule.subset_span ⟨φ, ?_⟩
    exact EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem (EigenSplit.isSplitting_complex E) σ φ v)
  obtain ⟨T, hT, hspan, hli⟩ := exists_linearIndependent ℂ T₀
  let b : Module.Basis T ℂ U := Module.Basis.mk hli (by rw [Subtype.range_coe, hspan, hS])
  have : Finite T := Module.Finite.finite_basis b
  have : Fintype T := Fintype.ofFinite T
  choose s hs using fun v : T => hT v.2
  have hb : ∀ a v, σ a (b v) = s v (a : E) • b v := fun a v => by
    simp only [b, Module.Basis.mk_apply]; exact hs v a
  let e := Fintype.equivFin T
  obtain ⟨k, hk⟩ := PeriodNonempty.exists_diag σ (fun i => s (e.symm i)) fun a => by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, e.symm.sum_comp fun v => s v (a : E)]
    simp [Matrix.trace, LinearMap.toMatrix_apply, hb]
  refine ⟨_, k, k.conjRingEquiv.toRingHom.comp σ, ⟨fun i => s (e.symm i), fun a z i => ?_⟩, fun a u => ?_⟩
  · obtain ⟨u, rfl⟩ := k.surjective z
    simpa using hk a u i
  · simp

section Hom

variable {Y : Type} [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]

theorem finrank_hom_complex : Module.finrank ℂ (Y →+ ℂ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).finrank_eq, Module.finrank_linearMap, Module.finrank_self, mul_one]

theorem finrank_hom_int : Module.finrank ℤ (Y →+ ℤ) = Module.finrank ℤ Y := by
  rw [(addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).finrank_eq]
  simp [Module.finrank_linearMap]

theorem span_intHom :
    Submodule.span ℂ (Set.range fun n : Y →+ ℤ => (Int.castAddHom ℂ).comp n) = ⊤ := by
  refine eq_top_iff.2 fun l _ => ?_
  let b := Module.Free.chooseBasis ℤ Y
  have : l = ∑ i, l (b i) • (Int.castAddHom ℂ).comp (b.coord i).toAddMonoidHom := by
    ext x
    conv_lhs => rw [← b.sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

end Hom

theorem zsmul_mem_Lam {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℤ) (z : Fin A.gB → ℂ)
    (h : ∀ l : A.abelian₂, ∃ n : ℤ, k * (A.H l z).im = n) : k • z ∈ A.abelian₂ := by
  choose n hn using h
  let φ : A.abelian₂ →+ ℤ := AddMonoidHom.mk' (fun l => -n l) fun l l' => by
    have : ((n (l + l') : ℤ) : ℝ) = n l + n l' := by
      rw [← hn, ← hn, ← hn, Submodule.coe_add, A.H_add_left, add_im, mul_add]
    have : n (l + l') = n l + n l' := by exact_mod_cast this
    simp only [this]; ring
  obtain ⟨l₀, hl₀⟩ := A.Ef_bij.2 φ.toIntLinearMap
  have h1 : ∀ l : A.abelian₂, imForm (sesq A.Hm) (l₀ - k • z) l = 0 := fun l => by
    have h2 : (A.Ef l₀ l : ℝ) = -n l := by rw [hl₀]; simp [φ]
    rw [map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
    change (A.H l₀ l).im - k • (A.H z l).im = 0
    rw [← A.Ef_eq_im, h2, ← hn, A.H_im_symm z l]
    simp
  have h3 : imForm (sesq A.Hm) (l₀ - k • z) = 0 := LinearMap.ext_on A.full fun l hl => h1 ⟨l, hl⟩
  have h4 : (l₀ : Fin A.gB → ℂ) - k • z = 0 := by
    by_contra hne
    have h5 := A.H_pos hne
    have h6 : (A.H (l₀ - k • z) (I • (l₀ - k • z))).im = 0 := congr($h3 (I • (l₀ - k • z)))
    rw [A.H_smul_right] at h6
    generalize A.H (l₀ - k • z) (l₀ - k • z) = c at h5 h6
    simp at h6
    linarith
  rw [← sub_eq_zero.1 h4]
  exact l₀.2

end GlobalTheory.OfPeriod
end
end

section
noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Complex

theorem exp_pi_I_int (n : ℤ) : Complex.exp (Real.pi * I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, mul_comm]; simp

variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W] [FiniteDimensional ℂ W]
  {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {O : Type} [CommRing O] [StarRing O]
  {Y M : Type} [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
  [AddCommGroup M] [Module O M] [Module.Free ℤ M] [Module.Finite ℤ M]

theorem exists_arc {w : O} (hw : w + star w = 1) (EM : LinearMap.BilinForm ℤ M) (hEM : Function.Bijective EM)
    (P : Y × (Y →+ ℤ) × M →+ W) (hspan : Submodule.span ℝ (Set.range P) = ⊤)
    (hrk : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ W)
    (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
    (hS : ∀ v v', (S (P v) (P v')).im = (v'.2.1 v.1 - v.2.1 v'.1 + EM v.2.2 v'.2.2 : ℤ))
    (ρ : O →+* Module.End ℂ W) (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w))
    (hP : ∀ (a : O) v, P (a • v.1, v.2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • v.2.2) = ρ a (P v))
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x y, be x y = be y x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : O) y x, be (a • y) x = be y (star a • x)) (be_even : ∀ x, (2 : ℤ) ∣ be x x)
    (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (A : AnArc O) (e : A.X ≃ₗ[O] Y) (f : M ≃+ A.abelian₂) (h : W ≃ₗ[ℂ] A.V),
      (∀ x y, A.be x y = be (e x) (e y)) ∧ (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam w l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (w • x))) ∧ Q A.gB A.F ∧ (∀ (a : O) m, f (a • m) = A.FLam a (f m)) ∧
      (∀ m m', A.Ef (f m) (f m') = EM m m') ∧ (∀ a z, h (ρ a z) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (AnArc.La.mk (e.symm v.1) (v.2.1.comp e.toAddEquiv.toAddMonoidHom) (f v.2.2))) ∧
      (A.BwMat 0).PosDef := by
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  let R : Submodule ℝ W := Submodule.span ℝ (Set.range fun n => P (0, n, 0))
  have hmem : ∀ n, P (0, n, 0) ∈ R := fun n => Submodule.subset_span ⟨n, rfl⟩
  have hRind : ∀ z, (∀ n, (S z (P (0, n, 0))).im = 0) → ∀ r ∈ R, (S z r).im = 0 := fun z hz r hr =>
    LinearMap.eqOn_span (f := imForm S z) (g := 0) (by rintro _ ⟨n, rfl⟩; exact hz n) hr
  have him : ∀ z z', (S z z').im = -(S z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0 := fun r hr => hRind r fun n => by
    rw [him, hRind _ (fun n' => by simp [hS]) r hr, neg_zero]
  have hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R := fun a r hr => by
    refine Submodule.span_le (p := R.comap ((ρ a).restrictScalars ℝ)).2 ?_ hr
    rintro _ ⟨n, rfl⟩
    show ρ a (P (0, n, 0)) ∈ R
    rw [← hP]
    simpa using hmem _
  obtain ⟨b, hb, hb'⟩ := exists_imPart hpos hR
  obtain ⟨n, q, j, F, hF, hqj, hj, hdec, hjq, hjF⟩ := exists_compl hpos hb hb' hρ hρR Q hQ
  have hjinj : Function.Injective j := Function.LeftInverse.injective hqj
  have hj' : ∀ z, ∀ r ∈ R, S r (j z) = 0 := fun z r hr => by rw [← hconj, hj z r hr, map_zero]
  have hbR : ∀ r ∈ R, b r = 0 := fun r hr =>
    imPart_eq hpos hb hb' R.zero_mem fun r' hr' => by simp [hR r hr r' hr']
  have hbI : ∀ r ∈ R, b (I • r) = r := fun r hr => imPart_eq hpos hb hb' hr fun r' hr' => by simp
  have hqR : ∀ r ∈ R, q r = 0 := fun r hr => hjinj (by simpa [hbR r hr, hbI r hr] using hdec r)
  have hqρ : ∀ a z, q (ρ a z) = F a (q z) := fun a z => by
    conv_lhs => rw [hdec z]
    simp only [map_add, map_smul, hqR _ (hρR _ _ (hb _)), ← hjF, hqj, smul_zero, zero_add]
  have hSq : ∀ z z', S z (j z') = S (j (q z)) (j z') := fun z z' => by
    conv_lhs => rw [hdec z]
    simp [hj' _ _ (hb _)]
  have hbm : ∀ v : Y × (Y →+ ℤ) × M, v.1 = 0 → b (P v) = 0 := fun v hv =>
    imPart_eq hpos hb hb' R.zero_mem fun r hr => by
      rw [hRind _ (fun n => by simp [hS, hv]) r hr]; simp

  let Φ : W → W → ℂ := fun z z' => S z (b z') - S (j (q z)) (j (q z')) / (2 * I)
  have hΦ : ∀ z z', Φ z z' = Φ z' z - (S z z').im := fun z z' =>
    sub_swap hconj hR hb (hj _) (hj _) (hdec z) (hdec z')
  have hΦρ : ∀ a z z', Φ (ρ a z) z' = Φ z (ρ (star a) z') := fun a z z' => by
    simp only [Φ, hqρ, hjF, hρ, imPart_act hpos hb hb' hρ hρR]
  let s : Y →+ W := P.comp (AddMonoidHom.inl _ _)
  have hs : ∀ y, s y = P (y, 0, 0) := fun _ => rfl
  have hsρ : ∀ (a : O) y, s (a • y) = ρ a (s y) := fun a y => by rw [hs, hs, ← hP]; simp
  let φ : W →ₗ[ℂ] (Y →+ ℂ) :=
    { toFun := fun z => AddMonoidHom.mk' (fun x => Φ z (s x)) fun x x' => by simp only [Φ, map_add]; ring
      map_add' := fun z z' => AddMonoidHom.ext fun x => by simp [Φ]; ring
      map_smul' := fun c z => AddMonoidHom.ext fun x => by simp [Φ]; ring }
  have hφ : ∀ z x, φ z x = Φ z (s x) := fun _ _ => rfl
  have hPv : ∀ v : Y × (Y →+ ℤ) × M, P v = s v.1 + P (0, v.2.1, 0) + P (0, 0, v.2.2) := fun v => by
    rw [hs, ← map_add, ← map_add]; simp
  have hφP : ∀ v x, φ (P v) x = φ (s v.1) x + v.2.1 x - S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I) :=
    fun v x => by
      have h1 : φ (P (0, v.2.1, 0)) x = v.2.1 x := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm, hqR _ (hmem _)]
      have h2 : φ (P (0, 0, v.2.2)) x = -(S (j (q (s x))) (j (q (P (0, 0, v.2.2)))) / (2 * I)) := by
        rw [hφ, hΦ, hs, hS]; simp [Φ, hbm]
      rw [hPv v, map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply, h1, h2]; ring
  have hr0 : ∀ r ∈ R, (∀ x, (S (s x) r).im = 0) → r = 0 := fun r hr h0 => by
    have h1 : (imForm S).flip r = 0 := LinearMap.ext_on_range hspan fun v => by
      show (S (P v) r).im = 0
      have h2 := congrArg Complex.re (hb' (P (0, 0, v.2.2)) r hr)
      rw [hbm _ rfl] at h2
      rw [hPv]
      simp only [map_add, LinearMap.add_apply, add_im, h0, hR _ (hmem _) r hr, zero_add]
      simpa using h2.symm
    by_contra hne
    have h3 : (S (I • r) r).im = 0 := congr($h1 (I • r))
    exact (hpos r hne).ne' (by simpa using h3)
  have hbij : Function.Bijective (φ.prod q) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro z hz
      have h1 : q z = 0 := congrArg Prod.snd hz
      have h2 : ∀ x, S z (b (s x)) = 0 := fun x => by
        have : φ z x = 0 := congr(($hz).1 x)
        simpa [hφ, Φ, h1] using this
      have h3 : ∀ x, (S (s x) (b (I • z))).im = 0 ∧ (S (s x) (b z)).im = 0 := fun x => by
        have := h2 x
        rw [hdec z, h1] at this
        simp only [map_add, map_smul, map_zero, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
          apply_imPart hconj hb' _ (hb _), smul_eq_mul] at this
        simpa [Complex.ext_iff] using this
      rw [hdec z, h1, hr0 _ (hb _) fun x => (h3 x).1, hr0 _ (hb _) fun x => (h3 x).2]
      simp
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨l, z⟩ -
      have h1 : ∀ l : Y →+ ℂ, (l, (0 : Fin n → ℂ)) ∈ LinearMap.range (φ.prod q) := fun l => by
        have : l ∈ (LinearMap.range (φ.prod q)).comap (LinearMap.inl ℂ _ _) := by
          refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := l)))
          rintro _ ⟨k, rfl⟩
          refine ⟨P (0, k, 0), Prod.ext (AddMonoidHom.ext fun x => ?_) (hqR _ (hmem k))⟩
          show φ _ x = _
          rw [hφP]
          simp [← Prod.zero_eq_mk]
        exact this
      have h2 : (l, z) = (l - φ (j z), 0) + φ.prod q (j z) := by simp [hqj]
      rw [h2]
      exact Submodule.add_mem _ (h1 _) ⟨_, rfl⟩
  let h : W ≃ₗ[ℂ] (Y →+ ℂ) × (Fin n → ℂ) := LinearEquiv.ofBijective _ hbij
  have hrk' : Module.finrank ℤ M = Module.finrank ℝ (Fin n → ℂ) := by
    have : Module.Finite ℂ (Y →+ ℂ) := Module.Finite.equiv (addMonoidHomLequivInt ℂ (A := Y) (B := ℂ)).symm
    have h1 := h.finrank_eq
    rw [Module.finrank_prod, finrank_hom_complex, Module.finrank_fin_fun] at h1
    rw [finrank_real_of_complex, Module.finrank_fin_fun]
    omega
  let SB : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ⋆[ℂ] ℂ := (S ∘ₗ j).compl₂ j
  have hSB : ∀ z z', SB z z' = S (j z) (j z') := fun _ _ => rfl
  let Hm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => SB (Pi.single i 1) (Pi.single k 1)
  have hHm : ∀ z z', hermForm Hm z z' = S (j z) (j z') := sesq_of SB
  let p : M →+ (Fin n → ℂ) :=
    q.toAddMonoidHom.comp (P.comp ((AddMonoidHom.inr _ _).comp (AddMonoidHom.inr _ _)))
  have hp : ∀ m, p m = q (P (0, 0, m)) := fun _ => rfl
  have hpE : ∀ m m', (S (j (p m)) (j (p m'))).im = EM m m' := fun m m' => by
    have h1 := hΦ (P (0, 0, m)) (P (0, 0, m'))
    simp only [Φ, hbm (0, 0, _) rfl, map_zero, hS, ← hp, AnArc.div_two_I] at h1
    have h2 := congrArg Complex.re h1
    simp [him (j (p m')) (j (p m))] at h2
    linarith
  have hpF : ∀ (a : O) m, p (a • m) = F a (p m) := fun a m => by
    rw [hp, hp, ← hqρ, ← hP]; simp
  obtain ⟨hpi, hpd, hps⟩ := PolarisedLattice.lattice_of_im EM hEM.1 p (fun z => SB.flip z) hpE hrk'
  let f : M ≃ₗ[ℤ] LinearMap.range p.toIntLinearMap := LinearEquiv.ofInjective p.toIntLinearMap hpi
  have hf : ∀ m, (f m : Fin n → ℂ) = p m := fun _ => rfl
  let Ef := LinearMap.BilinForm.congr f EM
  have hEf : ∀ m m', Ef (f m) (f m') = EM m m' := fun m m' => by
    rw [LinearMap.BilinForm.congr_apply, f.symm_apply_apply, f.symm_apply_apply]
  have hEadj : ∀ (a : O) m m', EM (a • m) m' = EM m (star a • m') := fun a m m' => by
    have : (EM (a • m) m' : ℝ) = EM m (star a • m') := by rw [← hpE, ← hpE, hpF, hpF, hjF, hjF, hρ]
    exact_mod_cast this
  have hEalt : ∀ m m', EM m m' = -EM m' m := fun m m' => by
    have : (EM m m' : ℝ) = -EM m' m := by rw [← hpE, ← hpE, him]
    exact_mod_cast this
  have hTs : ∀ x y, φ (s x) y = φ (s y) x := fun x y => by rw [hφ, hφ, hΦ, hs, hs, hS]; simp
  have hTa : ∀ (a : O) y x, φ (s (a • y)) x = φ (s y) (star a • x) := fun a y x => by
    rw [hφ, hφ, hsρ, hsρ, hΦρ]
  let A : AnArc O :=
    { gB := n
      abelian₂ := LinearMap.range p.toIntLinearMap
      discrete := hpd
      full := hps
      Hm := Hm
      Hm_herm := by ext i k; exact hconj _ _
      Hm_pos := fun z hz => by rw [hHm]; exact hpos _ fun h0 => hz (hjinj (by rw [h0, map_zero]))
      Ef := Ef
      Ef_eq := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        rw [hEf, hHm, hf, hf, hpE]
      Ef_bij := by
        have : (Ef : _ → _) = f.symm.dualMap ∘ EM ∘ f.symm := rfl
        rw [this]
        exact f.symm.dualMap.bijective.comp (hEM.comp f.symm.bijective)
      chi := fun l => (-1) ^ EM (w • f.symm l) (f.symm l)
      chi_norm := fun l => by simp
      chi_add := fun l m => by
        obtain ⟨l, rfl⟩ := f.surjective l
        obtain ⟨m, rfl⟩ := f.surjective m
        have h1 : EM (w • (l + m)) (l + m) =
            EM (w • l) l + EM (w • m) m + EM l m + 2 * (EM (w • l) m - EM l m) := by
          have h2 : EM (w • l) m + EM (star w • l) m = EM l m := by
            rw [← LinearMap.add_apply, ← map_add, ← add_smul, hw, one_smul]
          have h3 : EM (w • m) l = -EM (star w • l) m := by rw [hEadj, hEalt]
          simp only [smul_add, map_add, LinearMap.add_apply]
          linarith
        rw [hHm, hf, hf, hpE, exp_pi_I_int, ← map_add f]
        simp only [LinearEquiv.symm_apply_apply, h1, zpow_add₀ (neg_ne_zero.2 (one_ne_zero (α := ℂ))), zpow_mul]
        simp
      chi_neg := fun l => by simp only [map_neg, smul_neg, LinearMap.neg_apply, neg_neg]
      F := F
      F_mem := by rintro a _ ⟨m, rfl⟩; exact ⟨a • m, hpF a m⟩
      F_adj := fun a z z' => by rw [hHm, hHm, hjF, hjF, hρ]
      X := Y
      ct := q.toAddMonoidHom.comp s
      ct_smul := fun a x => by
        show q (s (a • x)) = F a (q (s x))
        rw [hsρ, hqρ]
      T := φ.toAddMonoidHom.comp s
      T_symm := hTs
      T_adj := hTa
      psi := fun x => Units.mk0 (eTwoPi (φ (s x) (w • x))) (AnArc.e_ne_zero _)
      psi_neg := fun x => by simp
      psi_add := fun x y => by
        have h2 : φ (s x) (w • y) + φ (s y) (w • x) = φ (s x) y := by
          rw [hTs y, hTa, ← map_add, ← add_smul, hw, one_smul]
        change eTwoPi _ = eTwoPi _ * eTwoPi _ * eTwoPi (φ (s x) y)
        simp only [← AnArc.e_add, smul_add, map_add, AddMonoidHom.add_apply]
        congr 1
        linear_combination h2
      be := be
      be_symm := be_symm
      be_pos := be_pos
      be_adj := be_adj
      be_even := be_even }
  have hfF : ∀ (a : O) m, f (a • m) = A.FLam a (f m) := fun a m => Subtype.ext (hpF a m)
  refine ⟨A, LinearEquiv.refl O Y, f.toAddEquiv, h, fun _ _ => rfl, fun l => ?_, fun _ => rfl, hF, hfF, hEf,
    fun a z => ?_, fun v => ?_, ?_⟩
  · obtain ⟨l, rfl⟩ := f.surjective l
    rw [← hfF]
    show (-1 : ℂ) ^ EM (w • f.symm (f l)) (f.symm (f l)) = (-1) ^ Ef (f (w • l)) (f l)
    rw [hEf, f.symm_apply_apply]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) (hqρ a z)
    show φ (ρ a z) x = φ z (star a • x)
    rw [hφ, hφ, hΦρ, hsρ]
  · refine Prod.ext (AddMonoidHom.ext fun x => ?_) ?_
    · show φ (P v) x = φ (s v.1) x + v.2.1 x - hermForm Hm (q (s x)) (p v.2.2) / (2 * I)
      rw [hφP, hHm, hp]
    · show q (P v) = q (s v.1) + p v.2.2
      rw [hPv, map_add, map_add, hqR _ (hmem _), add_zero, hp]
  · have hB : ∀ y x : Y, A.Bw 0 y x = (S (b (s y)) (b (s x))).re := fun y x => by
      show (φ (s y) x + 0 * (be y x : ℂ) + hermForm Hm (q (s y)) (q (s x)) / (2 * I)).im = _
      rw [hφ, hHm, hb' _ _ (hb _)]
      simp [Φ]
    let c := Module.Free.chooseBasis ℤ A.X
    refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx => ?_⟩
    · ext i k; simp [AnArc.BwMat_apply, A.Bw_symm 0 (Module.Free.chooseBasis ℤ A.X i)]
    · have h1 : ∑ i, x i • b (s (c i)) ≠ 0 := fun h0 => hx (funext fun k => by
        have h2 := congrArg (fun z => reForm S z (P (0, (c.coord k).toAddMonoidHom, 0))) h0
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, hb' _ _ (hmem _), hs,
          hS] at h2
        simpa [Finsupp.single_apply] using h2)
      refine (hpos _ h1).trans_eq ?_
      rw [← reForm_apply]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, reForm_apply, ← hB, dotProduct,
        Matrix.mulVec, AnArc.BwMat_apply, Finset.mul_sum, smul_eq_mul, star_trivial]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp only [c]; ring

end GlobalTheory.OfPeriod
end
end

section
noncomputable section

namespace GlobalTheory.OfPeriod

open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
open Complex

section Model

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem period_map_integer_vector (n : A.X →+ ℤ) : A.P0 (AnArc.La.mk 0 n 0) = ((Int.castAddHom ℂ).comp n, 0) := by
  ext <;> simp

theorem snd_eq_zero_iff (v : A.V) :
    v.2 = 0 ↔ v ∈ Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0)) := by
  constructor
  · intro hv
    have : v.1 ∈ (Submodule.span ℂ (Set.range fun n => A.P0 (AnArc.La.mk 0 n 0))).comap (LinearMap.inl ℂ _ _) := by
      refine (Submodule.span_le.2 ?_) (span_intHom.ge (Submodule.mem_top (x := v.1)))
      rintro _ ⟨n, rfl⟩
      exact Submodule.subset_span ⟨n, period_map_integer_vector A n⟩
    have h : v = LinearMap.inl ℂ _ _ v.1 := Prod.ext rfl hv
    rwa [h]
  · intro hv
    refine LinearMap.eqOn_span (f := LinearMap.snd ℂ _ _) (g := 0) ?_ hv
    rintro _ ⟨n, rfl⟩
    simp

theorem torusProj_eq_zero_iff {w : ℂ} (hw : (A.BwMat w).PosDef) (v : A.V) :
    A.torusProj v = 0 ↔ ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = 0 := by
  have h1 : ∀ n, A.Hw w v (A.P0 (AnArc.La.mk 0 n 0)) = A.dualForm w (A.torusProj v) ((Int.castAddHom ℂ).comp n) :=
    fun n => by rw [period_map_integer_vector, A.Hw_apply]; simp [AnArc.torusProj_def]
  simp only [h1]
  refine ⟨fun h n => by simp [h], fun h => ?_⟩
  have h2 : A.dualForm w (A.torusProj v) = 0 := LinearMap.ext_on_range span_intHom h
  by_contra hne
  have := A.dualForm_pos hw hne
  simp [h2] at this

theorem trace_actV {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (A : AnArc (𝓞 E))
    {ty : Fin A.gB → (E →+* ℂ)} (hF : ∀ a z i, A.F a z i = ty i (a : E) * z i) (a : 𝓞 E) :
    LinearMap.trace ℂ A.V (A.actV a) =
      (Module.finrank (𝓞 E) A.X : ℂ) * ∑ τ : E →+* ℂ, τ ((star a : 𝓞 E) : E) + ∑ i, ty i (a : E) := by
  let f : (A.X →+ ℂ) →ₗ[ℂ] (A.X →+ ℂ) := LinearMap.fst ℂ _ _ ∘ₗ A.actV a ∘ₗ LinearMap.inl ℂ _ _
  have h1 : A.actV a = f.prodMap (A.F a) := LinearMap.ext fun v => rfl
  have h2 : A.F a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
    LinearMap.ext fun z => funext fun i => by simp [hF, Matrix.mulVec_diagonal]
  rw [h1, LinearMap.trace_prodMap', HomTrace.trace_eq_finrank_mul_sum E A.X (star a) f fun _ _ => rfl, h2]
  simp

abbrev moduleLam : Module O A.abelian₂ where
  smul := A.FLam
  one_smul l := Subtype.ext (by show A.F 1 l = l; simp)
  mul_smul a b l := Subtype.ext (by show A.F (a * b) l = A.F a (A.F b l); simp)
  smul_zero a := Subtype.ext (map_zero (A.F a))
  smul_add a l m := Subtype.ext (map_add (A.F a) _ _)
  add_smul a b l := Subtype.ext (by show A.F (a + b) l = A.F a l + A.F b l; simp)
  zero_smul l := Subtype.ext (by show A.F 0 l = 0; simp)

end Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def perp (D : Datum H) (Hh : Submodule (𝓞 E) D.La) : Submodule (𝓞 E) D.La where
  carrier := {v | ∀ t ∈ Hh, D.EF t v = 0}
  zero_mem' t _ := map_zero _
  add_mem' {v v'} hv hv' t ht := by rw [map_add, hv t ht, hv' t ht, add_zero]
  smul_mem' a v hv t ht := by
    have h := D.adj (H.bar a) t v
    rw [hv _ (Hh.smul_mem _ ht)] at h
    have h2 : H.bar (H.bar a) = a := H.starRing.star_involutive a
    rw [h2] at h
    exact h.symm

theorem exists_datum_Lam : letI := H.starRing
    ∀ (A : AnArc (𝓞 E)) (p q : ℕ) (ty : Fin A.gB → (E →+* ℂ)), IsTypeFn H p q ty →
      (∀ a z i, A.F a z i = ty i (a : E) * z i) →
      ∃ (DB : Datum H) (e : DB.La ≃+ A.abelian₂), DB.p = p ∧ DB.q = q ∧ (∀ (a : 𝓞 E) x, e (a • x) = A.FLam a (e x)) ∧
        (∀ x x', DB.EF x x' = A.Ef (e x) (e x')) ∧
        IsPeriod DB ty (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddMonoidHom) := by
  let _ := H.starRing
  intro A p q ty hty hF
  let _ := moduleLam A
  have hr : Set.range A.abelian₂.subtype.toAddMonoidHom = A.abelian₂ := Subtype.range_coe
  have hd : ∀ G : AddSubgroup (Fin A.gB → ℂ), (G : Set (Fin A.gB → ℂ)) = A.abelian₂ → DiscreteTopology G := fun G hG => by
    have : G = A.abelian₂.toAddSubgroup := SetLike.coe_injective hG
    rw [this]; exact A.discrete
  obtain ⟨DB, e, hp, hq, he⟩ := PeriodDatum.exists_datum E H A.abelian₂ A.Ef p q A.gB ty A.abelian₂.subtype.toAddMonoidHom A.Hm hty
    A.Ef_bij A.Ef_FLam (fun a x i => hF a x i) Subtype.val_injective (hd _ hr) (hr ▸ A.full) A.Hm_herm A.Hm_pos
    fun x y => (A.Ef_eq x y).symm
  have hr' : Set.range (A.abelian₂.subtype.toAddMonoidHom.comp e.toAddEquiv.toAddMonoidHom) = A.abelian₂ :=
    (e.surjective.range_comp A.abelian₂.subtype.toAddMonoidHom).trans hr
  refine ⟨DB, e.toAddEquiv, hp, hq, e.map_smul, he, fun a x i => ?_, Subtype.val_injective.comp e.injective, hd _ hr',
    hr' ▸ A.full, A.Hm, A.Hm_herm, A.Hm_pos, fun x y => ?_⟩
  · exact (congrArg (fun l : A.abelian₂ => l.1 i) (e.map_smul a x)).trans (hF a _ i)
  · rw [he]; exact (A.Ef_eq _ _).symm

theorem exists_anArc_of_period (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : IsPeriod D ty P) {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y)
    (Hh : Submodule (𝓞 E) D.La) (hsat : ∀ (k : ℤ) (t : D.La), k ≠ 0 → k • t ∈ Hh → t ∈ Hh)
    (hiso : ∀ t ∈ Hh, ∀ t' ∈ Hh, D.EF t t' = 0)
    {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] (y : D.La →ₗ[𝓞 E] Y) (hy : Function.Surjective y)
    (hker : ∀ v, y v = 0 ↔ ∀ t ∈ Hh, D.EF t v = 0)
    (be : LinearMap.BilinForm ℤ Y) (be_symm : ∀ x x', be x x' = be x' x) (be_pos : ∀ x, x ≠ 0 → 0 < be x x)
    (be_adj : ∀ (a : 𝓞 E) x x', be (a • x) x' = be x (H.bar a • x')) (be_even : ∀ x, (2 : ℤ) ∣ be x x) :
    letI := H.starRing
    ∃ (A : AnArc (𝓞 E)) (e : A.X ≃ₗ[𝓞 E] Y) (gam : D.La ≃ₗ[𝓞 E] A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] A.V),
      (∀ x x', A.be x x' = be (e x) (e x')) ∧
      (∀ l, A.chi l = (-1) ^ A.Ef (A.FLam H.w0 l) l) ∧
      (∀ x, (A.psi x : ℂ) = eTwoPi (A.T x (H.w0 • x))) ∧
      (∀ v v', A.EF (gam v) (gam v') = D.EF v v') ∧
      (∀ v, e (gam v).y = y v) ∧
      (∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0) ∧
      (∀ (a : 𝓞 E) z, h (fun i => ty i (a : E) * z i) = A.actV a (h z)) ∧
      (∀ v, h (P v) = A.P0 (gam v)) ∧
      (A.BwMat 0).PosDef ∧
      (∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z') ∧
      (∀ z, (h z).2 = 0 ↔ z ∈ Submodule.span ℂ (P '' Hh)) ∧
      (∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0) ∧
      (∀ u u', (∀ t ∈ Hh, hermForm Hm u (P t) = 0) → A.H (h u).2 (h u').2 = hermForm Hm u u') ∧
      (∀ l, l ∈ A.abelian₂ ↔ ∃ v, y v = 0 ∧ (h (P v)).2 = l) ∧
      (∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0) ∧
      (∀ k : ℤ, (∀ v, y v = 0 → ∀ a ∈ Submodule.span ℝ (P '' Hh), (∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0) →
        k • a ∈ P '' Hh) → ∀ x, k • A.ct x ∈ A.abelian₂) ∧
      Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh ∧
      ∃ tyB : Fin A.gB → (E →+* ℂ), (∀ a z i, A.F a z i = tyB i (a : E) * z i) ∧
        (IsTypeFn H D.p D.q ty → Module.finrank (𝓞 E) Hh ≤ D.p ∧ Module.finrank (𝓞 E) Hh ≤ D.q ∧
          IsTypeFn H (D.p - Module.finrank (𝓞 E) Hh) (D.q - Module.finrank (𝓞 E) Hh) tyB ∧
          ∃ (DB : Datum H) (eB : DB.La ≃+ A.abelian₂), DB.p = D.p - Module.finrank (𝓞 E) Hh ∧
            DB.q = D.q - Module.finrank (𝓞 E) Hh ∧ (∀ (a : 𝓞 E) x, eB (a • x) = A.FLam a (eB x)) ∧
            (∀ x x', DB.EF x x' = A.Ef (eB x) (eB x')) ∧
            IsPeriod DB tyB (A.abelian₂.subtype.toAddMonoidHom.comp eB.toAddMonoidHom)) := by
  let _ := H.starRing
  obtain ⟨hlin, hinj, hdisc, hspan, Hm', hherm, hpos', hHm'⟩ := hP
  have hS : ∀ z z', sesq Hm z z' = sesq Hm' z z' := sesq_ext hspan fun i k => (hHm i k).trans (hHm' i k).symm
  have hconj : ∀ z z', starRingEnd ℂ (sesq Hm z z') = sesq Hm z' z := fun z z' => by
    rw [hS, hS, sesq_conj hherm]
  have hpos : ∀ z, z ≠ 0 → 0 < (sesq Hm z z).re := fun z hz => by rw [hS]; exact hpos' z hz
  have hw : H.w0 + star H.w0 = 1 := by
    show H.w0 + H.bar H.w0 = 1
    rw [HostModel.cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  have hadj : ∀ (a : 𝓞 E) x x', D.EF (a • x) x' = D.EF x (star a • x') := D.adj
  have halt : D.EF.IsAlt := D.alt
  obtain ⟨hfin, hrk, -⟩ := PeriodDatum.lattice_equiv P hinj hdisc hspan
  have : Module.IsTorsionFree ℤ D.La := hinj.moduleIsTorsionFree _ (map_zsmul P)
  have : Module.Finite ℤ Y := Module.Finite.of_surjective y.toAddMonoidHom.toIntLinearMap hy
  have : Module.IsTorsionFree ℤ Y := Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by
    obtain ⟨v, rfl⟩ := hy x
    refine or_iff_not_imp_left.2 fun hk => (hker v).2 fun t ht => ?_
    simpa [hk] using (hker (k • v)).1 (by rw [map_zsmul, hx]) t ht
  have : Module.Free ℤ Y := Module.free_of_finite_type_torsion_free'
  have := Forms.projective_of_int (𝓞 E) Y
  have hHh : ∀ t, t ∈ Hh ↔ ∀ v, y v = 0 → D.EF t v = 0 := fun t => by
    have : Module.Finite ℤ (D.La ⧸ Hh) :=
      Module.Finite.of_surjective Hh.mkQ.toAddMonoidHom.toIntLinearMap Hh.mkQ_surjective
    have : Module.IsTorsionFree ℤ (D.La ⧸ Hh) := Module.IsTorsionFree.of_smul_eq_zero fun k x hx => by
      obtain ⟨v, rfl⟩ := Hh.mkQ_surjective x
      refine or_iff_not_imp_left.2 fun hk => (Submodule.Quotient.mk_eq_zero _).2 (hsat k v hk ?_)
      exact (Submodule.Quotient.mk_eq_zero _).1 ((map_zsmul Hh.mkQ k v).trans hx)
    have : Module.Free ℤ (D.La ⧸ Hh) := Module.free_of_finite_type_torsion_free'
    refine ⟨fun ht v hv => (hker v).1 hv t ht, fun ht => (Submodule.Quotient.mk_eq_zero _).1 ?_⟩
    refine (KerPerp.ker_iff (hadj := hadj) (y := Hh.mkQ) D.unimod.2 t).2 fun v hv => ?_
    exact halt.eq_iff.1 (ht v ((hker v).2 fun t' ht' =>
      halt.eq_iff.1 (hv t' ((Submodule.Quotient.mk_eq_zero _).2 ht'))))
  obtain ⟨M, _, _, EM, e₀, hEM, he₁, he₂, he₃, hE⟩ := exists_split_of_coisotropic_ker (𝓞 E) D.La Y H.w0 D.EF y hw D.alt
    D.unimod hadj hy fun t ht => (hker t).2 fun t' ht' => hiso t' ht' t ((hHh t).2 ht)
  have : Module.Finite ℤ M := Module.Finite.of_surjective
    ((AddMonoidHom.snd _ _).comp ((AddMonoidHom.snd _ _).comp e₀.toAddMonoidHom)).toIntLinearMap
    fun m => ⟨e₀.symm (0, 0, m), by simp⟩
  have : Module.IsTorsionFree ℤ M := Function.Injective.moduleIsTorsionFree (fun m : M => e₀.symm (0, 0, m))
    (fun m m' hm => by simpa using hm) fun k m => by rw [← map_zsmul]; simp
  have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  have hrk' : 2 * Module.finrank ℤ Y + Module.finrank ℤ M = 2 * Module.finrank ℂ (Fin g → ℂ) := by
    have : Module.Finite ℤ (Y →+ ℤ) := Module.Finite.equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm
    have : Module.Free ℤ (Y →+ ℤ) := Module.Free.of_equiv (addMonoidHomLequivInt ℤ (A := Y) (B := ℤ)).symm
    rw [e₀.toIntLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, finrank_hom_int] at hrk
    rw [Module.finrank_fin_fun]
    omega
  let ρ : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) :=
    { toFun := fun a => LinearMap.pi fun i => ty i (a : E) • LinearMap.proj i
      map_one' := by ext; simp
      map_mul' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun _ _ => LinearMap.ext fun z => funext fun i => by simp [add_mul] }
  have hρ : ∀ a z, ρ a z = fun i => ty i (a : E) * z i := fun _ _ => rfl
  have hPρ : ∀ a v, P (a • v) = ρ a (P v) := fun a v => funext (hlin a v)
  have hρS : ∀ a z z', sesq Hm (ρ a z) z' = sesq Hm z (ρ (star a) z') := fun a =>
    sesq_ext (S := sesq Hm ∘ₗ ρ a) (S' := (sesq Hm).compl₂ (ρ (star a))) hspan fun v v' => by
      show (hermForm Hm (ρ a (P v)) (P v')).im = (hermForm Hm (P v) (ρ (star a) (P v'))).im
      rw [← hPρ, ← hPρ, hHm, hHm, hadj]
  have he : ∀ (a : 𝓞 E) v, e₀ (a • v) =
      (a • (e₀ v).1, (e₀ v).2.1.comp (DistribSMul.toAddMonoidHom Y (star a)), a • (e₀ v).2.2) := fun a v =>
    Prod.ext (by rw [he₁, he₁, map_smul]) (Prod.ext (AddMonoidHom.ext (he₂ a v)) (he₃ a v))
  obtain ⟨A, e, f, h, hbe, hchi, hpsi, ⟨tyB, hF⟩, hfF, hEf, hact, hh, hB⟩ := exists_arc hw EM hEM
    (P.comp e₀.symm.toAddMonoidHom)
    ((congrArg _ (e₀.symm.surjective.range_comp P)).trans hspan) hrk' hconj hpos
    (fun v v' => by
      show (hermForm Hm (P (e₀.symm v)) (P (e₀.symm v'))).im = _
      rw [hHm, hE, e₀.apply_symm_apply, e₀.apply_symm_apply]) ρ hρS
    (fun a v => by
      obtain ⟨v, rfl⟩ := e₀.surjective v
      rw [← he]
      simp [hPρ]) be be_symm be_pos be_adj be_even
    (fun n F => ∃ ty : Fin n → (E →+* ℂ), ∀ a z i, F a z i = ty i (a : E) * z i) exists_diag
  let gam : D.La ≃ₗ[𝓞 E] A.La :=
    { toFun := fun v => AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2)
      invFun := fun v => e₀.symm (e v.y, v.n.comp e.symm.toAddEquiv.toAddMonoidHom, f.symm v.l)
      map_add' := fun v v' => by ext <;> simp
      map_smul' := fun a v => by ext <;> simp [he, hfF]
      left_inv := fun v => e₀.injective (by ext <;> simp)
      right_inv := fun v => by ext <;> simp }
  have hgam : ∀ v, gam v =
      AnArc.La.mk (e.symm (e₀ v).1) ((e₀ v).2.1.comp e.toAddEquiv.toAddMonoidHom) (f (e₀ v).2.2) := fun _ => rfl
  have hiso' : ∀ v v', A.EF (gam v) (gam v') = D.EF v v' := fun v v' => by
    simp [hgam, AnArc.EF_apply, hEf, hE]
  have hgy : ∀ v, e (gam v).y = y v := fun v => by simp [hgam, he₁]
  have hgy0 : ∀ v, (gam v).y = 0 ↔ y v = 0 := fun v => by rw [← hgy, e.map_eq_zero_iff]
  have hgH : ∀ v, v ∈ Hh ↔ ∃ n, gam v = AnArc.La.mk 0 n 0 := fun v => by
    rw [hHh, ← A.orth_ker_iff_exists, gam.surjective.forall]
    simp only [hgy0, hiso']
  have hhP : ∀ v, h (P v) = A.P0 (gam v) := fun v => by simpa [hgam] using hh (e₀ v)
  have hP0 : ∀ v, A.Pw 0 v = A.P0 v := fun v => by simp [AnArc.Pw_apply]
  have hHw : ∀ z z', A.Hw 0 (h z) (h z') = hermForm Hm z z' :=
    sesq_ext (S := (A.Hw 0 ∘ₗ h.toLinearMap).compl₂ h.toLinearMap) (S' := sesq Hm) hspan fun v v' => by
      show (A.Hw 0 (h (P v)) (h (P v'))).im = (hermForm Hm (P v) (P v')).im
      rw [hhP, hhP, ← hP0, ← hP0, A.im_Hw_Pw hB, hiso', hHm]
  have himg : h '' (P '' Hh) = Set.range fun n => A.P0 (AnArc.La.mk 0 n 0) := by
    ext v
    constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      obtain ⟨n, hn⟩ := (hgH t).1 ht
      exact ⟨n, by rw [hhP, hn]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨_, ⟨gam.symm (AnArc.La.mk 0 n 0), (hgH _).2 ⟨n, by simp⟩, rfl⟩, by simp [hhP]⟩
  have hU : ∀ z, A.torusProj (h z) = 0 ↔ ∀ t ∈ Hh, hermForm Hm z (P t) = 0 := fun z => by
    rw [torusProj_eq_zero_iff A hB, ← Set.forall_mem_range (p := fun v => A.Hw 0 (h z) v = 0), ← himg]
    simp only [Set.forall_mem_image, hHw, SetLike.mem_coe]
  have hRind : ∀ z, (∀ t ∈ Hh, (sesq Hm z (P t)).im = 0) → ∀ r ∈ Submodule.span ℝ (P '' Hh), (sesq Hm z r).im = 0 :=
    fun z hz r hr => LinearMap.eqOn_span (f := imForm (sesq Hm) z) (g := 0) (by rintro _ ⟨t, ht, rfl⟩; exact hz t ht) hr
  have him : ∀ z z', (sesq Hm z z').im = -(sesq Hm z' z).im := fun z z' => by rw [← hconj z z', conj_im, neg_neg]
  have hperp : ∀ v, y v = 0 → ∀ t ∈ Hh, (sesq Hm (P v) (P t)).im = 0 := fun v hv t ht => by
    rw [him, sesq_apply, hHm, (hker v).1 hv t ht]; simp
  have hex : ∀ v, y v = 0 → ∃! a, a ∈ Submodule.span ℝ (P '' Hh) ∧ ∀ t ∈ Hh, hermForm Hm (P v - a) (P t) = 0 := by
    obtain ⟨b, hb, hb'⟩ := exists_imPart hpos (R := Submodule.span ℝ (P '' Hh)) fun r hr => hRind r fun t ht => by
      rw [him, hRind _ (hperp t ((hker t).2 fun t' ht' => hiso t' ht' t ht)) r hr, neg_zero]
    refine fun v hv => ⟨b (I • P v), ⟨hb _, fun t ht => ?_⟩, fun a ha => Eq.symm ?_⟩
    · rw [← sesq_apply, map_sub, LinearMap.sub_apply, hb' _ _ (Submodule.subset_span ⟨t, ht, rfl⟩)]
      apply Complex.ext <;> simp [hperp v hv t ht]
    · refine imPart_eq hpos hb hb' ha.1 fun r hr => ?_
      have := LinearMap.eqOn_span (f := reForm (sesq Hm) (P v - a)) (g := 0)
        (by rintro _ ⟨t, ht, rfl⟩; exact congrArg Complex.re (ha.2 t ht)) hr
      simp at this ⊢
      linarith
  have hrank : Module.finrank (𝓞 E) A.X = Module.finrank (𝓞 E) Hh := by
    have h1 : KerPerp.kerPerp hadj y = Hh := Submodule.ext fun t => (hHh t).symm
    have h2 := KerPerp.finrank_kerPerp hadj D.unimod hy
    have := D.fin
    have : Module.Finite (𝓞 E) Y := Module.Finite.of_surjective y hy
    rw [h1, finrank_int_eq_mul_of_finite (O := 𝓞 E), finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := Y)] at h2
    rw [e.finrank_eq, Nat.eq_of_mul_eq_mul_left Module.finrank_pos h2]
  refine ⟨A, e, gam, h, hbe, hchi, hpsi, hiso', hgy, hgH, hact, hhP, hB, hHw, fun z => ?_, hU, fun u u' hu => ?_,
    fun l => ⟨fun hl => ?_, ?_⟩, hex, fun k hk x => ?_, hrank, tyB, hF, fun hty => ?_⟩
  · rw [snd_eq_zero_iff, ← himg]
    exact Submodule.apply_mem_span_image_iff_mem_span (f := h.toLinearMap) h.injective
  · rw [← hHw, A.Hw_apply, (hU u).2 hu]; simp
  · exact ⟨gam.symm (AnArc.La.mk 0 0 ⟨l, hl⟩), (hgy0 _).1 (by simp), by simp [hhP]⟩
  · rintro ⟨v, hv, rfl⟩
    simp [hhP, (hgy0 v).2 hv]
  · refine zsmul_mem_Lam A k _ fun l => ?_
    obtain ⟨v, hv⟩ := gam.surjective (AnArc.La.mk 0 0 l)
    have hv0 : y v = 0 := (hgy0 v).1 (by simp [hv])
    obtain ⟨a, ⟨ha, ha'⟩, -⟩ := hex v hv0
    obtain ⟨t, ht, hta⟩ := hk v hv0 a ha ha'
    obtain ⟨n, hn⟩ := (hgH t).1 ht
    have h1 := congrArg (fun z => A.torusProj (h z) x) hta
    have h2 := congrArg (fun r => r x) ((hU _).2 ha')
    simp only [map_sub, map_zsmul, hhP, hv, hn, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply,
      AnArc.torusProj_periodZero_eq_real, AddMonoidHom.zero_apply] at h1 h2
    rw [← sub_eq_zero.1 h2] at h1
    refine ⟨n x, ?_⟩
    simpa using (congrArg Complex.re h1).symm
  · obtain ⟨h1, h2, h3⟩ := ComplementTypes.types E H D.p D.q (Module.finrank (𝓞 E) Hh) g A.gB ty tyB hty fun a => by
      have h4 : A.actV a = h.conj (ρ a) := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply, hact]
      have h5 : ρ a = Matrix.toLin' (Matrix.diagonal fun i => ty i (a : E)) :=
        LinearMap.ext fun z => funext fun i => by simp [hρ, Matrix.mulVec_diagonal]
      have h6 := trace_actV A hF a
      rw [h4, LinearMap.trace_conj', h5, hrank] at h6
      refine Eq.trans ?_ h6
      simp
    exact ⟨h1, h2, h3, exists_datum_Lam A _ _ tyB h3 hF⟩

open HostModel in

example (H : Host E) {g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H 1 1 ty) : letI := H.starRing
    ∃ (P : (hypDatum H).La →+ (Fin g → ℂ)) (A : AnArc (𝓞 E)) (_ : A.X ≃ₗ[𝓞 E] 𝓞 E)
      (gam : (hypDatum H).La ≃ₗ[𝓞 E] A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] A.V),
      IsPeriod (hypDatum H) ty P ∧ ∀ v, h (P v) = A.P0 (gam v) := by
  obtain ⟨P, hP⟩ := PeriodNonempty.exists_isPeriod E H (hypDatum H) g ty hty
  obtain ⟨Hm, -, -, hHm⟩ := hP.2.2.2.2
  obtain ⟨A, e, gam, h, -, -, -, -, -, -, -, hh, -⟩ := exists_anArc_of_period (hypDatum H) hP hHm
    (LinearMap.ker (LinearMap.fst _ _ _)) (fun k t hk ht => by simpa [hk] using ht)
    (fun t ht t' ht' => by simp [show t.1 = 0 from ht, show t'.1 = 0 from ht'])
    (LinearMap.fst _ _ _) LinearMap.fst_surjective
    (fun v => ⟨fun hv t ht => by simp [show t.1 = 0 from ht, show v.1 = 0 from hv],
      fun hv => (Module.forall_dual_apply_eq_zero_iff ℤ v.1).1 fun φ => by
        simpa using hv (0, (ConjDual.toDual H).symm φ) rfl⟩)
    ((2 : ℤ) • trForm H) (fun x x' => congrArg (2 * ·) (trForm_symm H x x'))
    (fun x hx => mul_pos two_pos (trForm_pos H hx)) (fun a x x' => congrArg (2 * ·) (trForm_adj H a x x'))
    fun x => ⟨_, rfl⟩
  exact ⟨P, A, e, gam, h, hP, hh⟩

end GlobalTheory.OfPeriod
end
end
