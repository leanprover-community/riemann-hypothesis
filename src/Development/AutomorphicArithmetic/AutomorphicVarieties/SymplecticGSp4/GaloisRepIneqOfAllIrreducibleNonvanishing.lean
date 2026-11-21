import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ASmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.QuotientSaturatedSquareTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TriComb
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DiagCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsLiftOfDerivationOnIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormLeOneOfIsIntegral

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem wcomp_self_eq_of_mem_wtPart {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp]
  by_cases h1 : Finsupp.weight wt n = j
  · rw [if_pos h1]
  · rw [if_neg h1]
    exact (hf' n h1).symm

private theorem wcomp_eq_zero_of_mem_wtPart_of_ne {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) {j' : X} (hj : j' ≠ j) : wcomp O wt j' f = 0 := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp, map_zero]
  by_cases h1 : Finsupp.weight wt n = j'
  · rw [if_pos h1]
    exact hf' n (by rw [h1]; exact hj)
  · rw [if_neg h1]

private theorem aGraded_internal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (M : Model D) : DirectSum.IsInternal M.gr := by
  have key : ∀ (n : ℤ) (x : M.R), x ∈ M.aPart n → x ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) → x = 0 := by
    intro n x hx hx'
    have hle : (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) ≤
        Submodule.map M.W.π.toLinearMap
          (LinearMap.ker (M.W.π.toLinearMap ∘ₗ wcomp c.O M.W.wt ((0 : ℤ), n))) := by
      refine iSup₂_le fun m hm => ?_
      rintro y ⟨h, hh, rfl⟩
      refine ⟨h, ?_, rfl⟩
      change M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) h) = 0
      rw [wcomp_eq_zero_of_mem_wtPart_of_ne hh, map_zero]
      intro h'
      exact hm (Prod.ext_iff.mp h').2.symm
    obtain ⟨g, hg, hgx⟩ := hle hx'
    obtain ⟨f, hf, rfl⟩ := hx
    have hker : f - g ∈ RingHom.ker M.W.π := by
      rw [RingHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr hgx.symm
    have h2 := M.W.homog _ hker ((0 : ℤ), n)
    rw [RingHom.mem_ker, map_sub, map_sub] at h2
    have hg' : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) = 0 := hg
    have h3 : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) = M.W.π f := by
      rw [wcomp_self_eq_of_mem_wtPart hf]
    change M.W.π f = 0
    calc M.W.π f = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) := h3.symm
      _ = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) := sub_eq_zero.mp h2
      _ = 0 := hg'
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro n
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : (x : M.R) ∈ M.aPart n := hx
    have h2 : (x : M.R) ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) := by
      have := Submodule.mem_map_of_mem (f := M.A.val.toLinearMap) hx'
      simp only [Submodule.map_iSup] at this
      exact (iSup₂_mono fun m _ => Submodule.map_comap_le _ _) this
    exact Subtype.ext (key n _ h1 h2)
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy⟩ := x
    have main : ∀ (z : M.R) (hz : z ∈ ⨆ n, M.aPart n), (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n := by
      intro z hz
      refine Submodule.iSup_induction' M.aPart
        (motive := fun z hz => (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n) ?_ ?_ ?_ hz
      · intro n w hw
        exact Submodule.mem_iSup_of_mem n hw
      · exact zero_mem _
      · intro a b ha hb iha ihb
        exact add_mem iha ihb
    exact main y hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aGraded :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, Nonempty (GradedAlgebra M.gr) := by
  intro Ω _ _ _ l _ c D _ M
  exact ⟨{ (inferInstance : SetLike.GradedMonoid M.gr), (aGraded_internal M).chooseDecomposition with }⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem aW_comb {σ : Type} [Fintype σ] (lam : σ → ℤ) (hl : ∀ s, lam s = -1 ∨ lam s = 0 ∨ lam s = 1)
    (P : (σ →₀ ℕ) → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (h1 : ∀ s, lam s = 0 → P (Finsupp.single s 1))
    (h2 : ∀ s t, lam s = 1 → lam t = -1 → P (Finsupp.single s 1 + Finsupp.single t 1)) :
    ∀ m, Finsupp.weight lam m = 0 → P m := by
  classical
  intro m
  induction m using WellFoundedLT.induction with
  | ind m ih =>
  intro hm
  have step : ∀ g : σ →₀ ℕ, g ≠ 0 → g ≤ m → Finsupp.weight lam g = 0 → P g → P m := fun g hg hle hw hP => by
    have e : m - g + g = m := tsub_add_cancel_of_le hle
    have hlt : m - g < m := by
      conv_rhs => rw [← e]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hg)
    have hw' : Finsupp.weight lam (m - g) = 0 := by
      have := congrArg (Finsupp.weight lam) e
      rwa [map_add, hw, add_zero, hm] at this
    rw [← e]
    exact hadd _ _ (ih _ hlt hw') hP
  by_cases hz : ∃ s, m s ≠ 0 ∧ lam s = 0
  · obtain ⟨s, hs, hs0⟩ := hz
    refine step (Finsupp.single s 1) (by simp) ?_ (by simp [Finsupp.weight_single, hs0]) (h1 s hs0)
    rw [Finsupp.single_le_iff]
    omega
  by_cases hp : (∃ s, m s ≠ 0 ∧ lam s = 1) ∧ ∃ t, m t ≠ 0 ∧ lam t = -1
  · obtain ⟨⟨s, hs, hs1⟩, t, ht, ht1⟩ := hp
    have hst : s ≠ t := by
      rintro rfl
      omega
    refine step _ (by simp) ?_ (by simp [Finsupp.weight_single, hs1, ht1]) (h2 s t hs1 ht1)
    intro u
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    split_ifs with a b b
    · exact absurd (a.trans b.symm) hst
    · subst a; omega
    · subst b; omega
    · omega
  have hsum : ∑ s, (m s : ℤ) * lam s = 0 := by
    rw [← hm, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  have : m = 0 := by
    ext u
    push Not at hz
    rcases not_and_or.1 hp with hp | hp
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, (m s : ℤ) * lam s ≤ 0 := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonpos hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
    · push Not at hp
      have hn : ∀ s ∈ Finset.univ, 0 ≤ (m s : ℤ) * lam s := fun s _ => by
        by_cases h : m s = 0
        · simp [h]
        · have := hl s; have := hp s h
          exact mul_nonneg (by positivity) (by omega)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hsum u (Finset.mem_univ _)
      by_contra h
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h (by exact_mod_cast h4)
      · exact hz u h h4
  rw [this]
  exact h0

private theorem aW_wts : ∀ w ∈ wts, (w.1 = -1 ∨ w.1 = 0 ∨ w.1 = 1) ∧ (-1 ≤ w.2 ∧ w.2 ≤ 1) := by decide

private theorem aW_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (B : Subalgebra O R) (h0 : ∀ x ∈ W.part 0, x ∈ B)
    (h1 : ∀ s, (W.wt s).1 = 0 → W.z s ∈ B)
    (h2 : ∀ s t, (W.wt s).1 = 1 → (W.wt t).1 = -1 → W.z s * W.z t ∈ B) (n : ℤ) :
    ∀ x ∈ W.part (0, n), x ∈ B := by
  have hmon : ∀ m, Finsupp.weight (fun s => (W.wt s).1) m = 0 → W.π (MvPowerSeries.monomial m 1) ∈ B := by
    refine aW_comb _ (fun s => (aW_wts _ (hw s)).1) _ (by simp) (fun a b ha hb => ?_) h1 (fun s t hs ht => ?_)
    · have := mul_mem ha hb
      rwa [← map_mul, MvPowerSeries.monomial_mul_monomial, one_mul] at this
    · have := h2 s t hs ht
      rwa [WPres.z, WPres.z, ← map_mul, MvPowerSeries.X_def, MvPowerSeries.X_def,
        MvPowerSeries.monomial_mul_monomial, one_mul] at this
  have hfst : ∀ m : W.σ →₀ ℕ, Finsupp.weight (fun s => (W.wt s).1) m = (Finsupp.weight W.wt m).1 := fun m => by
    induction m using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb, Prod.fst_add]
    | single s k => simp [Finsupp.weight_single]
  obtain ⟨μ, hμ, hdec⟩ := part_span O R (ℤ × ℤ) W {m | Finsupp.weight W.wt m = (0, n)} (0, n) (fun _ h => h)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨b, hb, rfl⟩ := hdec f hf
  show W.π _ ∈ _
  rw [map_sum]
  refine sum_mem fun m hm => ?_
  rw [map_mul]
  refine mul_mem (h0 _ ⟨b m, hb m, rfl⟩) (hmon m ?_)
  have : Finsupp.weight W.wt m = (0, n) := hμ hm
  rw [hfst, this]

private theorem weight_algebra_generated_degree_two {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O (ℤ × ℤ) R)
    (hw : ∀ s, W.wt s ∈ wts) (a : ℤ → Submodule O R) [SetLike.GradedMonoid a] (ha : ∀ n, a n = W.part (0, n)) :
    ∃ s : Finset (gradedSub a), (∀ x ∈ s, x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧
      Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ s) = ⊤ := by
  classical
  let U : Set R := Set.range W.z ∪ Set.range fun p : W.σ × W.σ => W.z p.1 * W.z p.2
  have hU : U.Finite := (Set.finite_range _).union (Set.finite_range _)
  let T : Set (gradedSub a) := {x | (x.1 ∈ a (-2) ∨ x.1 ∈ a (-1) ∨ x.1 ∈ a 1 ∨ x.1 ∈ a 2) ∧ x.1 ∈ U}
  have hT : T.Finite := (hU.preimage Subtype.val_injective.injOn).subset fun x hx => hx.2
  refine ⟨hT.toFinset, fun x hx => (hT.mem_toFinset.1 hx).1, ?_⟩
  rw [hT.coe_toFinset]
  set S := Algebra.adjoin O ({x : gradedSub a | x.1 ∈ a 0} ∪ T) with hS
  have key : ∀ n : ℤ, -2 ≤ n → n ≤ 2 → ∀ y ∈ W.part (0, n), y ∈ U → y ∈ S.map (gradedSub a).val := by
    intro n hn hn' y hy hyU
    rw [← ha] at hy
    refine ⟨⟨y, le_iSup a n hy⟩, Algebra.subset_adjoin ?_, rfl⟩
    have h4 : n = 0 ∨ n = -2 ∨ n = -1 ∨ n = 1 ∨ n = 2 := by omega
    rcases h4 with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hy
    · exact Or.inr ⟨Or.inl hy, hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inl hy), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inl hy)), hyU⟩
    · exact Or.inr ⟨Or.inr (Or.inr (Or.inr hy)), hyU⟩
  have main := aW_gen W hw (S.map (gradedSub a).val)
    (fun y hy => by
      have hy' : y ∈ a 0 := by rw [ha]; exact hy
      exact ⟨⟨y, le_iSup a 0 hy'⟩, Algebra.subset_adjoin (Or.inl hy'), rfl⟩)
    (fun s hs => by
      have hb := (aW_wts _ (hw s)).2
      refine key (W.wt s).2 (by omega) (by omega) _ ?_ (Or.inl ⟨s, rfl⟩)
      rw [← hs]
      exact W.z_mem s)
    (fun s t hs ht => by
      have hb := (aW_wts _ (hw s)).2
      have hb' := (aW_wts _ (hw t)).2
      refine key ((W.wt s).2 + (W.wt t).2) (by omega) (by omega) _ ?_ (Or.inr ⟨(s, t), rfl⟩)
      have h5 : W.z s * W.z t ∈ W.part (W.wt s + W.wt t) :=
        SetLike.GradedMul.mul_mem (W.z_mem s) (W.z_mem t)
      have h6 : W.wt s + W.wt t = (0, (W.wt s).2 + (W.wt t).2) :=
        Prod.ext (by rw [Prod.fst_add, hs, ht]; rfl) rfl
      rwa [h6] at h5)
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  have hxS : x ∈ S.map (gradedSub a).val :=
    Submodule.iSup_induction a (motive := fun x => x ∈ S.map (gradedSub a).val) hx (fun n y hy => main n y (ha n ▸ hy))
      (zero_mem _) (fun a b ha hb => add_mem ha hb)
  obtain ⟨y, hy, hxy⟩ := hxS
  obtain rfl : y = ⟨x, hx⟩ := Subtype.ext hxy
  exact hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aW :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], IsWRing M.gr M.x0 := by
  intro Ω _ _ _ l _ c D _ M _
  classical
  have hz : ∀ s, M.W.z s ∈ maximalIdeal M.R := fun s => by
    rw [← res_eq_zero_iff c.O, ← res_map (M.W.origin M.org), WPres.z, M.W.origin_π, MvPowerSeries.constantCoeff_X,
      map_zero]
  refine ⟨?_, ?_, ?_⟩
  · haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal c.O (ℤ × ℤ) M.R M.W hz
    let p : M.W.gr 0 →ₐ[c.O] M.gr 0 :=
      { toFun := fun F => ⟨⟨F.1.1, M.aPart_le (n := 0) F.2⟩, F.2⟩
        map_one' := rfl
        map_mul' := fun F G => rfl
        map_zero' := rfl
        map_add' := fun F G => rfl
        commutes' := fun c => rfl }
    haveI : Nontrivial (M.gr 0) := ⟨⟨0, 1, fun h =>
      zero_ne_one (α := M.R) (congrArg (fun x : M.gr 0 => ((x : M.A) : M.R)) h)⟩⟩
    refine co_quot c.O (M.W.gr 0) (M.gr 0) p ?_
    rintro ⟨⟨x, hxA⟩, hx⟩
    exact ⟨⟨⟨x, M.W.part_le_A (j := 0) hx⟩, hx⟩, rfl⟩
  · exact weight_algebra_generated_degree_two M.W M.wt_mem M.aPart (fun _ => rfl)
  · rintro j hj f ⟨g, hg, hgf⟩
    have hgf' : M.W.π g = (f : M.R) := hgf
    show M.W.origin M.org (f : M.R) = 0
    rw [← hgf', M.W.origin_π, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hg 0 (by rw [map_zero]; exact fun h => hj (congrArg Prod.snd h).symm)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem fg_map_mk {O A S : Type} [CommRing O] [IsNoetherianRing O] [CommRing A] [Algebra O A] [CommRing S]
    [Algebra O S] (f : A →ₐ[O] S) (I : Ideal A) (hI : ∀ a, f a = 0 ↔ a ∈ I) (P : Submodule O A) (T : Submodule O S)
    (hT : T.FG) (hP : ∀ a ∈ P, f a ∈ T) : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).FG := by
  have hIf : ∀ a ∈ I, f a = 0 := fun a ha => (hI a).mpr ha
  let g : A ⧸ I →ₐ[O] S := Ideal.Quotient.liftₐ I f hIf
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hI a).mp hy
  haveI : IsNoetherian O T := isNoetherian_of_fg_of_noetherian T hT
  have hle : (P.map (Ideal.Quotient.mkₐ O I).toLinearMap).map g.toLinearMap ≤ T := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact hP a ha
  exact Submodule.fg_of_fg_map_injective g.toLinearMap hg (isNoetherian_submodule.mp inferInstance _ hle)

theorem UpperTheory.V.GradeZeroInterpolatingElement.m2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], D.Fin0 → M2 M.gr M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hF
  obtain ⟨h1, -, h3⟩ := kerA D hD M
  have hs := spanMono D hD M hF 0
  have hfin := hF M.S M.ru M.pt
  have hT : (Subalgebra.toSubmodule (Algebra.adjoin c.O (mono M.ru.hom 0))).FG :=
    Module.Finite.iff_fg.1 hfin
  refine fg_map_mk (M.SS.val.comp M.toSS) _ (fun a => ?_) _ _ hT (fun a ha => ?_)
  · rw [← h1 a]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · have h4 : (M.toSS a).1 ∈ M.sPart 0 := h3 0 a ha
    rw [hs] at h4
    exact Algebra.span_le_adjoin _ _ h4
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem linked_iff_torus_conjugate {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (i j : Fin 4) : Ge r i j ↔ Ge r' i j := by
  unfold Ge
  refine exists_congr fun g => ?_
  rw [h g]
  simp [tconj]

private theorem torus_conjugate_corner_entry_eq {H K : Type} [Group H] [Field K] {r r' : H →* M4 K} {t : Kˣ × Kˣ}
    (h : ∀ g, r g = tconj t (r' g)) (g : H) : r g 0 0 = r' g 0 0 := by
  rw [h g]
  simp [tconj, wv, wt]

private theorem diagonal_type_corner_cases {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hS : SoV Ω l) (hF : D.Fin0)
    (ξ : M.SS →ₐ[c.O] PadicAlgCl l) (hd : DiagType (M.rep ξ)) :
    (M.rep ξ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr (ξ.comp M.toSS)) ∨
    (M.rep ξ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr (ξ.comp M.toSS)) := by
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ
  obtain ⟨s1, s2, -⟩ := signs D hD M hF ξ
  have hd' : DiagType r := fun i j hij a b => hd i j hij ((linked_iff_torus_conjugate h i j).1 a) ((linked_iff_torus_conjugate h j i).1 b)
  have hs : (D.s0 : G ℚ Ω) ∈ D.Ip l := hD.decompSigma_mem.1.1
  rcases diagCases D hD hS r hr hd' with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s1 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩
  · exact Or.inr ⟨(torus_conjugate_corner_entry_eq h _).symm.trans (a _ hs), s2 fun i j hij e => b i j hij ((linked_iff_torus_conjugate h i j).2 e)⟩

theorem UpperTheory.V.GradeZeroInterpolatingElement.m3 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], Loc.LocalPublishedTheorems → SoV Ω l → D.Fin0 → M3 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal := by
  intro Ω _ _ _ l _ c D hD M _ hL hS hF x₁ h1 hn hp _
  obtain ⟨ξ₁, rfl⟩ := ptLift D hD M x₁ h1
  obtain ⟨t, r, hr, h⟩ := ptScale D hD M hF ξ₁
  obtain ⟨-, -, s3, -, s5⟩ := signs D hD M hF ξ₁
  have n02 : ¬ Ge r 0 2 := fun e => s3 hp ((linked_iff_torus_conjugate h 0 2).1 e)
  have hd : DiagType (M.rep ξ₁) := by
    rcases tri D hD hL r hr with a | a | a
    · obtain ⟨p1, -, -, -, -, p6, -⟩ := ptIn D hD _ r hr
      exact absurd ((geAlg _ r _ p1 p6).2.2.2.2.1.1 a 0 2) n02
    · exact fun i j hij u v => a i j hij ((linked_iff_torus_conjugate h i j).2 u) ((linked_iff_torus_conjugate h j i).2 v)
    · exact absurd a.1 n02
  have hne : ((D.th D.s0 : c.O) : PadicAlgCl l) ≠ ((D.al D.s0 : c.O) : PadicAlgCl l) := fun e => by
    have hinj := (facts D hD).2.2.2.2.2.2.1
    have : (0 : Fin 4) = 2 := hinj (Subtype.ext e)
    exact absurd this (by decide)
  have key : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → Same0 M.gr x (ξ₁.comp M.toSS) →
      (M.rep ξ₁ D.s0 0 0 = ((D.th D.s0 : c.O) : PadicAlgCl l) ∧ NegZero M.gr x) ∨
      (M.rep ξ₁ D.s0 0 0 = ((D.al D.s0 : c.O) : PadicAlgCl l) ∧ PosZero M.gr x) := by
    intro x hx h0
    obtain ⟨ξ, rfl⟩ := ptLift D hD M x hx
    obtain ⟨q1, q2⟩ := s5 ξ fun b hb => (h0 b hb).symm
    rw [q1]
    exact diagonal_type_corner_cases D hD M hS hF ξ (q2 hd)
  rcases diagonal_type_corner_cases D hD M hS hF ξ₁ hd with ⟨a, -⟩ | ⟨a, -⟩
  · refine Or.inr ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨-, b⟩ | ⟨b, -⟩
    · exact hnn b
    · exact hne (a.symm.trans b)
  · refine Or.inl ?_
    rintro ⟨x, hx, -, hnn, h0⟩
    rcases key x hx h0 with ⟨b, -⟩ | ⟨-, b⟩
    · exact hne (b.symm.trans a)
    · exact hnn b
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem kill_of_len {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [AddCommGroup M]
    [Module O M] (h : Module.length O M ≠ ⊤) : ∃ b : O, b ≠ 0 ∧ ∀ x : M, b • x = 0 := by
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 (Module.length_ne_top_iff.1 h)
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsArtinian.range_smul_pow_stabilizes M p
  have h1 := hn (n + 1) (Nat.le_succ n)
  have h2 : LinearMap.range (p ^ n • LinearMap.id : M →ₗ[O] M) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal O) _ (IsNoetherian.noetherian _) ?_
      (maximalIdeal_le_jacobson _)
    intro y hy
    rw [h1] at hy
    obtain ⟨x, rfl⟩ := hy
    have : (p ^ (n + 1) • LinearMap.id : M →ₗ[O] M) x = p • (p ^ n • LinearMap.id : M →ₗ[O] M) x := by
      simp [smul_smul, pow_succ']
    rw [this]
    exact Submodule.smul_mem_smul ((mem_maximalIdeal _).2 hp.not_isUnit) ⟨x, rfl⟩
  refine ⟨p ^ n, pow_ne_zero _ hp.ne_zero, fun x => ?_⟩
  have : (p ^ n • LinearMap.id : M →ₗ[O] M) x ∈ (⊥ : Submodule O M) := h2 ▸ ⟨x, rfl⟩
  simpa using this

section Abs

variable {O W Γ : Type} [CommRing O] [AddCommGroup W] [Module O W] [TopologicalSpace W] [DiscreteTopology W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W] [Group Γ] [TopologicalSpace Γ]

private theorem exists_norm (θ : Γ →* Oˣ) (hc : ∀ m : W, Continuous fun g => (θ g : O) • m) (g0 : Γ)
    (hu : IsUnit ((θ g0 : O) - 1)) :
    ∃ N : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W), Function.Injective N ∧ (∀ x, IsLocallyConstant (N x)) ∧
      (∀ x g h, N x (g * h) = N x g + (θ g : O) • N x h) ∧ (∀ x, N x g0 = 0) ∧
      ∀ (𝒟 : Set (Subgroup Γ)) x, x ∈ LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 → ∀ D ∈ 𝒟, ∃ m : W, ∀ g ∈ D,
        N x g = (θ g : O) • m - m := by
  obtain ⟨u, hu⟩ := hu
  let t : Γ → (⊤ : Subgroup Γ) := fun g => ⟨g, trivial⟩
  let n : Z1U (Formalism.GaloisCohomology.scalRep W θ) ⊤ →ₗ[O] (Γ → W) :=
    { toFun := fun z g => z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0)
      map_add' := fun z z' => by
        funext g
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        abel
      map_smul' := fun r z => by
        funext g
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_sub, RingHom.id_apply, smul_smul]
        congr 2
        ring }
  have hn : ∀ z g, n z g = z.1 (t g) - ((θ g : O) - 1) • ((u⁻¹ : Oˣ) : O) • z.1 (t g0) := fun _ _ => rfl
  have hker : ∀ z, n z = 0 ↔ ∃ m : W, ∀ g : (⊤ : Subgroup Γ), z.1 g = (θ g : O) • m - m := fun z => by
    constructor
    · intro h
      refine ⟨((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g => ?_⟩
      have := congrFun h g
      rw [hn, Pi.zero_apply, sub_eq_zero, sub_smul, one_smul] at this
      exact this
    · rintro ⟨m, hm⟩
      funext g
      have e : z.1 (t g0) = (u : O) • m := by rw [hm, hu, sub_smul, one_smul]
      rw [hn, e, smul_smul _ _ m, Units.inv_mul, one_smul, hm, sub_smul, one_smul]
      exact sub_self _
  refine ⟨Submodule.liftQ _ n fun z hz => (hker z).2 ((mem_coboundaries1 _ _).1 hz), ?_, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ((hker z).1 hx))
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [IsLocallyConstant.iff_continuous]
    show Continuous (n z)
    have h1 : Continuous fun g => z.1 (t g) := z.2.1.comp (continuous_id.subtype_mk _)
    refine (h1.sub ((hc (((u⁻¹ : Oˣ) : O) • z.1 (t g0))).sub (continuous_const (y := ((u⁻¹ : Oˣ) : O) • z.1 (t g0))))).congr fun g => ?_
    rw [hn, sub_smul, one_smul]
    rfl
  · intro x g h
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show n z _ = n z _ + _ • n z _
    have e : z.1 (t (g * h)) = z.1 (t g) + (θ g : O) • z.1 (t h) := z.2.2 (t g) (t h)
    rw [hn, hn, hn, e, map_mul, Units.val_mul]
    module
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show n z _ = 0
    rw [hn, ← hu, smul_smul, Units.mul_inv, one_smul, sub_self]
  · intro 𝒟 x hx D hD
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
    refine ⟨m - ((u⁻¹ : Oˣ) : O) • z.1 (t g0), fun g hg => ?_⟩
    show n z _ = _
    have e : z.1 (t g) = (θ g : O) • m - m := hm (t g) hg
    rw [hn, e]
    module

omit [TopologicalSpace W] [DiscreteTopology W] [IsTopologicalAddGroup W] [ContinuousConstSMul O W] in
private theorem exists_j (a : O) (w : W) (hw : ∀ y : O, y • w = 0 ↔ a ∣ y) (hg : ∀ w' : W, a • w' = 0 → ∃ y : O, w' = y • w) :
    ∃ (ι : (O ⧸ Ideal.span {a}) →ₗ[O] W) (j : W → O ⧸ Ideal.span {a}), Function.Injective ι ∧
      ∀ m, a • m = 0 → ι (j m) = m := by
  let ι : (O ⧸ Ideal.span {a}) →ₗ[O] W := Submodule.liftQ (Ideal.span {a}) (LinearMap.toSpanSingleton O W w)
    fun y hy => (hw y).2 (Ideal.mem_span_singleton.1 hy)
  refine ⟨ι, Function.invFun ι, ?_, fun m hm => Function.invFun_eq ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 (Ideal.mem_span_singleton.2 ((hw y).1 hx))
  · obtain ⟨y, rfl⟩ := hg m hm
    exact ⟨Submodule.Quotient.mk y, rfl⟩

private theorem main_abs [IsDomain O] (θ : Γ →* Oˣ) (hc : ∀ m : W, Continuous fun g => (θ g : O) • m) (g0 : Γ)
    (hu : IsUnit ((θ g0 : O) - 1)) (𝒟 : Set (Subgroup Γ)) (b : O) (hb : b ≠ 0)
    (hk : ∀ x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟, b • x = 0) (T : Finset ℕ) (Gp : ℕ → Subgroup Γ)
    (hG : ∀ v ∈ T, Gp v ∈ 𝒟 ∧ ∃ s ∈ Gp v, θ s ≠ 1)
    (hW : ∀ a : O, a ≠ 0 → ∃ w : W, (∀ y : O, y • w = 0 ↔ a ∣ y) ∧ ∀ w' : W, a • w' = 0 → ∃ y : O, w' = y • w) :
    ∃ a : O, a ≠ 0 ∧ ∃ Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a}), Function.Injective Z ∧
      ∀ x, IsLocallyConstant (Z x) ∧ (∀ g h, Z x (g * h) = Z x g + Ideal.Quotient.mk _ (θ g : O) * Z x h) ∧
        (∀ D ∈ 𝒟, ∀ g ∈ D, θ g = 1 → Z x g = 0) ∧ Z x g0 = 0 ∧
        ∀ v ∈ T, ∃ m : O ⧸ Ideal.span {a}, ∀ g ∈ Gp v, Z x g = Ideal.Quotient.mk _ (θ g : O) * m - m := by
  obtain ⟨N, hi, hl, hco, h0, hloc⟩ := exists_norm θ hc g0 hu
  choose! s hs hs1 using fun v hv => (hG v hv).2
  let a : O := b * ∏ v ∈ T, ((θ (s v) : O) - 1)
  have ha : a ≠ 0 := mul_ne_zero hb (Finset.prod_ne_zero_iff.2 fun v hv h =>
    hs1 v hv (Units.ext (sub_eq_zero.1 h)))
  obtain ⟨w, hw, hg⟩ := hW a ha
  obtain ⟨ι, j, hι, hj⟩ := exists_j a w hw hg
  have hbN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, b • N x g = 0 := fun x g => by
    have h1 : b • (x : H1U (Formalism.GaloisCohomology.scalRep W θ) ⊤) = 0 := congrArg Subtype.val (hk x)
    have h2 := congrFun (map_smul N b x.1) g
    rw [h1, map_zero] at h2
    exact h2.symm
  have haN : ∀ (x : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟) g, ι (j (N x g)) = N x g := fun x g =>
    hj _ (by
      show (b * _) • _ = _
      rw [mul_comm b, mul_smul, hbN, smul_zero])
  have hmul : ∀ (r : O) (q : O ⧸ Ideal.span {a}), ι (Ideal.Quotient.mk _ r * q) = r • ι q := fun r q =>
    map_smul ι r q
  let Z : LocSel (Formalism.GaloisCohomology.scalRep W θ) ⊤ 𝒟 →+ (Γ → O ⧸ Ideal.span {a}) := AddMonoidHom.mk' (fun x g => j (N x g))
    fun x y => funext fun g => hι (by
      show ι (j (N (x + y).1 g)) = ι (j (N x.1 g) + j (N y.1 g))
      rw [ι.map_add, haN, haN, haN, Submodule.coe_add, N.map_add, Pi.add_apply])
  have hZ : ∀ x g, ι (Z x g) = N x g := haN
  refine ⟨a, ha, Z, fun x y h => Subtype.ext (hi (funext fun g => by rw [← hZ, ← hZ, h])), fun x =>
    ⟨(hl x).comp j, fun g h => hι ?_, fun D hD g hg h1 => hι ?_, hι ?_, fun v hv => ?_⟩⟩
  · rw [map_add, hmul, hZ, hZ, hZ, hco]
  · obtain ⟨m, hm⟩ := hloc 𝒟 x x.2 D hD
    rw [hZ, hm g hg, h1, map_zero, Units.val_one, one_smul, sub_self]
  · rw [hZ, h0, map_zero]
  · obtain ⟨m, hm⟩ := hloc 𝒟 x x.2 _ (hG v hv).1
    have h1 : a • m = 0 := by
      have e : (((θ (s v) : O) - 1)) • m = N x (s v) := by rw [hm _ (hs v hv), sub_smul, one_smul]
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun v => (θ (s v) : O) - 1) hv
      have : a = d * (b * ((θ (s v) : O) - 1)) := by
        show b * _ = _
        rw [hd]; ring
      rw [this, mul_smul, mul_smul, e, hbN, smul_zero]
    refine ⟨j m, fun g hg => hι ?_⟩
    rw [hZ, map_sub, hmul, hj m h1, hm g hg]

end Abs

section Conc

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)

private theorem isUnit_inverse_character_sub_one (hD : D.Good) : IsUnit (((D.Psi⁻¹ D.g0 : c.Oˣ) : c.O) - 1) := by
  rw [MonoidHom.inv_apply]
  have h1 : IsUnit (1 - (D.Psi D.g0 : c.O)) := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one]
    exact fun h => hD.genElt_Psi (sub_eq_zero.1 h).symm
  have := (Units.isUnit (D.Psi D.g0)⁻¹).mul h1
  rwa [mul_sub, mul_one, Units.inv_mul] at this

private theorem local_group_in_family_nontrivial (hD : D.Good) (v : ℕ) (hv : v ∈ D.T) :
    D.Gp v ∈ shaFam ℚ Ω (∏ p ∈ D.S, p) ∧ ∃ s ∈ D.Gp v, D.Psi⁻¹ s ≠ 1 := by
  obtain ⟨-, -, -, -, hP, -, hinj, -⟩ := facts D hD
  have hθ1 : ∀ g, D.Psi⁻¹ g = 1 ↔ D.Psi g = 1 := fun g => by rw [MonoidHom.inv_apply, inv_eq_one]
  have hvS : v ∈ D.S := by
    rcases Finset.mem_insert.1 hv with h | h
    · exact h ▸ hD.l_mem
    · classical exact (Finset.mem_filter.1 h).1
  refine ⟨Chr.shaFam_mono (Finset.dvd_prod_of_mem (fun p => p) hvS)
    (Or.inl ⟨D.pl v, hD.pl_over v (hD.S_prime v hvS), rfl⟩), ?_⟩
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]
    refine ⟨D.s0, D.s0.2, fun h => ?_⟩
    have h1 : D.ps 1 D.s0 = D.ps 3 D.s0 := (hθ1 _).1 h
    have h2 : (1 : Fin 4) = 3 := hinj (congrArg Units.val h1)
    exact absurd h2 (by decide)
  · by_contra hne
    have h1 : (D.Ip v).map D.ψ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro s hs
      by_contra h2
      exact hne ⟨s, hs.1, fun h3 => h2 (((hP v h s hs).2.1).symm.trans ((hθ1 _).1 h3))⟩
    have h3 : l ∣ Nat.card ((D.Ip v).map D.ψ) := by classical exact (Finset.mem_filter.1 h).2.2
    rw [h1, Subgroup.card_bot] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

private theorem cont_Psi (hD : D.Good) (m : QO l c.O) : Continuous fun g => ((D.Psi⁻¹ g : c.Oˣ) : c.O) • m := by
  have hθ : D.Psi⁻¹ = D.ψ⁻¹ * chiO ℚ Ω l c.O ^ (-(D.e : ℤ)) := Chr.Psi_inv l D.e D.ψ
  have hker : (D.ψ⁻¹).ker = D.ψ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.inv_apply, inv_eq_one]
  have hc := (contTw ℚ Ω l).2.2 c.O D.ψ⁻¹ (-(D.e : ℤ)) (by rw [hker]; exact hD.psi_open)
  rw [← hθ] at hc
  exact (continuous_prod_of_discrete_right.1 hc) m

private theorem conc (hD : D.Good) (ρ : Representation c.O (G ℚ Ω) (QO l c.O)) (hρ : ρ = twist₂ l D.Psi⁻¹)
    (hfin : Module.length c.O (ShaU ρ (∏ p ∈ D.S, p) ⊤) ≠ ⊤) :
    ∃ a : c.O, a ≠ 0 ∧ ∃ Z : ShaU ρ (∏ p ∈ D.S, p) ⊤ →+ (G ℚ Ω → c.O ⧸ Ideal.span {a}), Function.Injective Z ∧
      ∀ x, D.ShaCoc a (Z x) := by
  subst hρ
  have hU := (facts D hD).2.2.1 1
  have q1 := (ML.qoCyc l c.O).2.1
  have q2 := (ML.qoCyc l c.O).2.2.1
  have HH := fun b hb hk => main_abs (W := QO l c.O) D.Psi⁻¹ (cont_Psi D hD) D.g0 (isUnit_inverse_character_sub_one D hD)
    (shaFam ℚ Ω (∏ p ∈ D.S, p)) b hb hk D.T D.Gp (local_group_in_family_nontrivial D hD)
    (fun a ha => (q1 a ha).imp fun w hw => ⟨hw, q2 a w ha hw⟩)
  refine (kill_of_len hfin).elim fun b hb => (HH b hb.1 hb.2).imp fun a h => ⟨h.1, h.2.imp fun Z hZ => ⟨hZ.1, fun x => ?_⟩⟩
  have H := hZ.2 x
  refine ⟨H.1, H.2.1, fun A hA g hg hr => H.2.2.1 _ (Or.inr ⟨A, rfl⟩) g hg ?_, H.2.2.2.1, H.2.2.2.2⟩
  rw [MonoidHom.inv_apply, inv_eq_one]
  exact hU A hA g hg hr

end Conc

theorem UpperTheory.V.GradeZeroInterpolatingElement.shaCoc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoFin Ω l → D.sha ≠ ⊤ ∧ ∃ a : c.O, a ≠ 0 ∧ ∃ Z : ShaU (Chr.rho l D.e D.ψ) (∏ p ∈ D.S, p) ⊤ →+ (G ℚ Ω → c.O ⧸ Ideal.span {a}), Function.Injective Z ∧ ∀ x, D.ShaCoc a (Z x) := by
  intro Ω _ _ _ l _ c D hD hS
  have hfin : D.sha ≠ ⊤ := ne_top_of_le_ne_top (hS c D.ψ hD.psi_open D.e (le_trans one_le_two hD.two_le))
    (Chr.VS_anti l (Finset.dvd_prod_of_mem (fun p => p) hD.l_mem) D.e D.ψ)
  exact ⟨hfin, conc D hD _ (Chr.rho_eq l D.e D.ψ) hfin⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem der_zero {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι] [DecidableEq ι] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (I : Ideal O) (d : R →ₗ[O] O) (hd : d ∈ PtDer x O) (h0 : ∀ f, π f = 0 → d f ∈ I)
    (h1 : ∀ g i j, ∃ f, π f = r.hom g i j ∧ d f ∈ I) (f : R) : d f ∈ I := by
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ I)) := co_sqz O O _ fun _ => rfl
  have hd' : I.mkQ ∘ₗ d ∈ PtDer x (O ⧸ I) := fun f g => by
    have := hd f g
    simp only [LinearMap.comp_apply, this, map_add, map_smul]
  obtain ⟨y, hy⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, hd', rfl⟩
  obtain ⟨y', hy'⟩ := (der_hom O R O (O ⧸ I) x _).1 ⟨_, (PtDer x (O ⧸ I)).zero_mem, rfl⟩
  have key : ∀ f, d f ∈ I ↔ y f = y' f := fun f => by
    rw [TrivSqZeroExt.ext_iff, (hy f).1, (hy f).2, (hy' f).1, (hy' f).2]
    simp only [true_and, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have k' : ∀ f, π f = 0 → y' f = 0 := fun f hf => TrivSqZeroExt.ext (by rw [(hy' f).1, hx f hf]; rfl) (by rw [(hy' f).2]; rfl)
  have k : ∀ f, π f = 0 → y f = 0 := fun f hf => ((key f).1 (h0 f hf)).trans (k' f hf)
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ).symm
  have he : ∀ f, e (π f) = Ideal.Quotient.mk _ f := fun f => by
    simp only [e]; rw [AlgEquiv.symm_apply_eq]; rfl
  let u : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y k).comp e.toAlgHom
  let u' : S →ₐ[O] TrivSqZeroExt O (O ⧸ I) := (Ideal.Quotient.liftₐ (RingHom.ker π) y' k').comp e.toAlgHom
  have hu : ∀ f, u (π f) = y f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y k (e (π f)) = _
    rw [he]; rfl
  have hu' : ∀ f, u' (π f) = y' f := fun f => by
    show Ideal.Quotient.liftₐ (RingHom.ker π) y' k' (e (π f)) = _
    rw [he]; rfl
  have huu : u = u' := hr _ u u' (Lift.ext (MonoidHom.ext fun g => Matrix.ext fun i j => by
    obtain ⟨f, hf, hf'⟩ := h1 g i j
    rw [Lift.map_hom, Lift.map_hom, ← hf, hu, hu', (key f).1 hf']))
  rw [key, ← hu, ← hu', huu]

private theorem wt_eq_neg (i j : Fin 4) : wt i j = -wPs → (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by revert i j; decide

private theorem origin_part {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
    (h : W.HasOrigin) {j : X} (hj : j ≠ 0) {f : R} (hf : f ∈ W.part j) : W.origin h f = 0 := by
  obtain ⟨p, hp, rfl⟩ := hf
  have := hp 0 (by rw [map_zero]; exact hj.symm)
  rw [AlgHom.toLinearMap_apply, WPres.origin_π]
  simpa using this

private theorem len_le (hM : LemmaM') {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] [IsAdicComplete (maximalIdeal O) O]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)}
    {R S : Type} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S] [IsCO O S] (π : R →ₐ[O] S)
    (hπ : Function.Surjective π) (r : Lift O rbar S) (hr : r.Generates) (x : R →ₐ[O] O) (hx : ∀ f, π f = 0 → x f = 0)
    (P : ℤ × ℤ → Submodule O R) (hom : ∀ g i j, ∃ f ∈ P (wt i j), π f = r.hom g i j)
    (A : Subalgebra O R) (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (hA : ∀ n (f : A), f ∈ 𝒜 n ↔ f.1 ∈ P (0, n))
    (hA' : ∀ n f, f ∈ P (0, n) → f ∈ A) (hx1 : ∀ f ∈ P (0, -1), x f = 0)
    {ι : Type} (F : ι → A) (hF : ∀ i, F i ∈ 𝒜 (-1)) (hF0 : ∀ i, π (F i) = 0)
    (a : O) (ha : a ≠ 0) (N : Type) [AddCommGroup N] [Module O N] (Z : N →+ (Γ → O ⧸ Ideal.span {a}))
    (hZ : Function.Injective Z) (s t : Γ → Oˣ)
    (der : ∀ μ, ∃ δ ∈ PtDer x O, HasWt P (-wPs) δ ∧ (∀ f, π f = 0 → δ f ∈ Ideal.span {a}) ∧
      ∀ g f, (π f = r.hom g 2 0 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (s g : O) * Z μ g) ∧
        (π f = r.hom g 3 1 → Ideal.Quotient.mk _ (δ f) = Ideal.Quotient.mk _ (t g : O) * Z μ g)) :
    Module.length O N ≤ cotLen (x.comp A.val) 𝒜 (-1) F := by
  choose δ h1 h2 h3 h4 using der
  have hadd : ∀ μ ν f, Ideal.Quotient.mk (Ideal.span {a}) (δ (μ + ν) f) =
      Ideal.Quotient.mk _ (δ μ f) + Ideal.Quotient.mk _ (δ ν f) := fun μ ν f => by
    rw [← map_add, Ideal.Quotient.eq]
    refine der_zero π hπ r hr x hx (Ideal.span {a}) (δ (μ + ν) - (δ μ + δ ν))
      (sub_mem (h1 _) (add_mem (h1 _) (h1 _)))
      (fun f hf => sub_mem (h3 _ f hf) (add_mem (h3 _ f hf) (h3 _ f hf))) (fun g i j => ?_) f
    obtain ⟨f, hf, hf'⟩ := hom g i j
    refine ⟨f, hf', ?_⟩
    show δ (μ + ν) f - (δ μ f + δ ν f) ∈ _
    by_cases hw : wt i j = -wPs
    · rw [← Ideal.Quotient.eq, map_add]
      rcases wt_eq_neg i j hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [(h4 _ g f).1 hf', (h4 _ g f).1 hf', (h4 _ g f).1 hf', map_add, Pi.add_apply, mul_add]
      · rw [(h4 _ g f).2 hf', (h4 _ g f).2 hf', (h4 _ g f).2 hf', map_add, Pi.add_apply, mul_add]
    · rw [h2 _ _ hw f hf, h2 _ _ hw f hf, h2 _ _ hw f hf]; simp
  let Dm : N →+ (A →ₗ[O] O ⧸ Ideal.span {a}) :=
    AddMonoidHom.mk' (fun μ => (Ideal.span {a}).mkQ ∘ₗ δ μ ∘ₗ A.val.toLinearMap) fun μ ν =>
      LinearMap.ext fun f => hadd μ ν f
  have hDm : ∀ μ (f : A), Dm μ f = Ideal.Quotient.mk _ (δ μ f) := fun _ _ => rfl
  refine hM O A ℤ 𝒜 (x.comp A.val) (-1) (fun f hf => hx1 _ ((hA _ f).1 hf)) ι F hF a ha N Dm ?_ (fun μ i => ?_)
    fun μ => ⟨δ μ ∘ₗ A.val.toLinearMap, fun f g => h1 μ f g, fun n hn f hf => ?_, fun f => rfl⟩
  · refine (injective_iff_map_eq_zero Dm).2 fun μ hμ => hZ ?_
    rw [map_zero]
    funext g
    obtain ⟨f, hf, hf'⟩ := hom g 2 0
    have e1 := hDm μ ⟨f, hA' (-1) f (by rwa [show wt 2 0 = (0, -1) by decide] at hf)⟩
    rw [hμ, LinearMap.zero_apply, (h4 μ g f).1 hf'] at e1
    exact ((s g).isUnit.map (Ideal.Quotient.mk (Ideal.span {a}))).mul_right_eq_zero.1 e1.symm
  · rw [hDm, Ideal.Quotient.eq_zero_iff_mem]
    exact h3 μ _ (hF0 i)
  · exact h2 μ (0, n) (fun h => hn (congrArg Prod.snd h)) _ ((hA n f).1 hf)

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.mPrime :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ [GradedAlgebra M.gr], LemmaM' → SoFin Ω l → D.sha ≤ cotLen M.x0 M.gr (-1) M.eqns.F := by
  intro Ω _ _ _ l _ c D hD M _ hM hS
  obtain ⟨-, a, ha, Z, hZ, hc⟩ := shaCoc D hD hS
  haveI : Finite (ResidueField c.O) := by
    obtain ⟨-, -, h, -⟩ := dvrFacts l c.O
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ PadicInt.residueField.symm.toEquiv
    exact IsLocalRing.ResidueField.finite_of_finite ‹_›
  have hx : ∀ f, M.π f = 0 → M.W.origin M.org f = 0 := fun f hf => by
    obtain ⟨e, -, he⟩ := M.hom 1 0 0
    have h1 := M.at0 1 0 0 (f + e) (by rw [map_add, hf, he, zero_add])
    rw [map_add, M.at0 1 0 0 e he] at h1
    exact add_eq_right.1 h1
  exact len_le hM M.π M.surj M.ru M.gen (M.W.origin M.org) hx M.W.part M.hom M.A M.gr (fun _ _ => Iff.rfl)
    (fun n f hf => M.aPart_le hf) (fun f hf => origin_part M.W M.org (by decide) hf) M.eqns.F M.eqns.hF
    (fun i => by
      show M.F i ∈ RingHom.ker M.π
      rw [M.ker]
      exact Ideal.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))
    a ha _ Z hZ D.th D.Psi fun μ => M.der a (Z μ) ha (hc μ)
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.aElt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ g, ∃ a ∈ M.gr 0, M.x0 a = 0 ∧ ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ) := by
  intro Ω _ _ _ l _ c D _ M g
  choose f hf hπ using fun i : Fin 4 => M.hom g i i
  have hf0 : ∀ i, f i ∈ M.aPart 0 := by
    intro i
    have h := hf i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact h
  let fA : Fin 4 → M.A := fun i => ⟨f i, M.aPart_le (hf0 i)⟩
  have hx0 : ∀ i, M.x0 (fA i) = D.r0 g i i := fun i => M.at0 g i i (f i) (hπ i)
  have hss : ∀ i, M.toSS (fA i) = M.ent g i i := fun i => Subtype.ext (hπ i)
  refine ⟨∑ i, fA i - algebraMap c.O M.A (Matrix.trace (D.r0 g)), ?_, ?_, ?_⟩
  · apply Submodule.sub_mem
    · exact Submodule.sum_mem _ fun i _ => hf0 i
    · rw [Algebra.algebraMap_eq_smul_one]
      apply Submodule.smul_mem
      show (1 : M.R) ∈ M.aPart 0
      exact SetLike.GradedOne.one_mem
  · rw [map_sub, map_sum, AlgHom.commutes]
    simp only [hx0, Algebra.algebraMap_self, RingHom.id_apply, Matrix.trace, Matrix.diag]
    exact sub_self _
  · intro ξ
    rw [map_sub, map_sub, map_sum, map_sum, AlgHom.commutes, AlgHom.commutes]
    simp only [hss, Raw.aVal, Matrix.trace, Matrix.diag, map_sum]
    rfl
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.nval :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l), IsNVal c.O (PadicAlgCl l) fun x => -Real.log ‖x‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  intro l _ c
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : 0 < Real.log l := Real.log_pos hl
  have he : (0 : ℝ) ≤ ((eO l c.O).toNat : ℝ) := Nat.cast_nonneg _
  have anti : ∀ a b : PadicAlgCl l, a ≠ 0 → ‖a‖ ≤ ‖b‖ →
      -Real.log ‖b‖ * ((eO l c.O).toNat : ℝ) / Real.log l ≤
        -Real.log ‖a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
    intro a b ha hab
    have hlog : Real.log ‖a‖ ≤ Real.log ‖b‖ := Real.log_le_log (norm_pos_iff.mpr ha) hab
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_right (by linarith) he
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    ring
  · intro x y hx hy hxy
    have h := IsUltrametricDist.norm_add_le_max x y
    rcases le_total ‖x‖ ‖y‖ with h1 | h1
    · rw [max_eq_right h1] at h
      exact (min_le_right _ _).trans (anti _ _ hxy h)
    · rw [max_eq_left h1] at h
      exact (min_le_left _ _).trans (anti _ _ hxy h)
  · intro a ha
    have h := normO l c.O a ha
    have h2 := congrArg Real.log h
    rw [Real.log_pow, Real.log_pow, Real.log_inv] at h2
    show -Real.log ‖(a : PadicAlgCl l)‖ * ((eO l c.O).toNat : ℝ) / Real.log l = _
    field_simp
    linarith
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

private theorem add_lt {K : Type} [NormedField K] [IsUltrametricDist K] {a b : K} {M : ℝ} (ha : ‖a‖ < M) (hb : ‖b‖ < M) :
    ‖a + b‖ < M := (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem sub_lt {K : Type} [NormedField K] [IsUltrametricDist K] {a b : K} {M : ℝ} (ha : ‖a‖ < M) (hb : ‖b‖ < M) :
    ‖a - b‖ < M := by
  rw [sub_eq_add_neg]; exact add_lt ha (by rwa [norm_neg])

private theorem sum_lt {K : Type} [NormedField K] [IsUltrametricDist K] (f : Fin 4 → K) {M : ℝ} (h : ∀ k, ‖f k‖ < M) :
    ‖∑ k, f k‖ < M := by
  rw [Fin.sum_univ_four]; exact add_lt (add_lt (add_lt (h _) (h _)) (h _)) (h _)

private theorem block_of_intertwine {K : Type} [NormedField K] [IsUltrametricDist K] (X X' u : M4 K) (d : Fin 4 → K)
    (hX : ∀ i j, ‖X i j - Matrix.diagonal d i j‖ < 1) (hX' : ∀ i j, ‖X' i j - Matrix.diagonal d i j‖ < 1)
    (hb : IsBlock X) (hb' : IsBlock X') (hd : ∀ i j, lamW i ≠ lamW j → 1 ≤ ‖d i - d j‖) (h : u * X = X' * u) : IsBlock u := by
  classical
  obtain ⟨⟨i, j⟩, hij, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun p : Fin 4 × Fin 4 => lamW p.1 ≠ lamW p.2)
    (fun p => ‖u p.1 p.2‖) ⟨(0, 1), by decide⟩
  have hij' : lamW i ≠ lamW j := (Finset.mem_filter.1 hij).2
  have hm : ∀ a b, lamW a ≠ lamW b → ‖u a b‖ ≤ ‖u i j‖ := fun a b hab =>
    hmax (a, b) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩)
  by_cases h0 : u i j = 0
  · intro a b hab
    have := hm a b hab
    rw [h0, norm_zero] at this
    exact norm_le_zero_iff.1 this
  exfalso
  have hpos : 0 < ‖u i j‖ := norm_pos_iff.2 h0
  have e : (d i - d j) * u i j = (u * (X - Matrix.diagonal d)) i j - ((X' - Matrix.diagonal d) * u) i j := by
    rw [Matrix.mul_sub, Matrix.sub_mul, h, Matrix.sub_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  have t1 : ‖(u * (X - Matrix.diagonal d)) i j‖ < ‖u i j‖ := by
    rw [Matrix.mul_apply]
    refine sum_lt _ fun k => ?_
    by_cases hk : lamW k = lamW j
    · rw [norm_mul]
      have h1 := hm i k (hk ▸ hij')
      have h2 := hX k j
      rw [Matrix.sub_apply]
      calc _ ≤ ‖u i j‖ * ‖X k j - Matrix.diagonal d k j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < ‖u i j‖ := mul_lt_of_lt_one_right hpos h2
    · have hkj : k ≠ j := fun hh => hk (hh ▸ rfl)
      rw [Matrix.sub_apply, hb k j hk, Matrix.diagonal_apply_ne _ hkj]
      simpa using h0
  have t2 : ‖((X' - Matrix.diagonal d) * u) i j‖ < ‖u i j‖ := by
    rw [Matrix.mul_apply]
    refine sum_lt _ fun k => ?_
    by_cases hk : lamW i = lamW k
    · rw [norm_mul]
      have h1 := hm k j (hk ▸ hij')
      have h2 := hX' i k
      rw [Matrix.sub_apply]
      calc _ ≤ ‖X' i k - Matrix.diagonal d i k‖ * ‖u i j‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ < ‖u i j‖ := mul_lt_of_lt_one_left hpos h2
    · have hkj : i ≠ k := fun hh => hk (hh ▸ rfl)
      rw [Matrix.sub_apply, hb' i k hk, Matrix.diagonal_apply_ne _ hkj]
      simpa using h0
  have t3 := sub_lt t1 t2
  rw [← e, norm_mul] at t3
  exact absurd t3 (not_lt.2 (le_mul_of_one_le_left hpos.le (hd i j hij')))

private theorem ne_of_close {K : Type} [NormedField K] [IsUltrametricDist K] {a b a' b' : K} (ha : ‖a - a'‖ < 1)
    (hb : ‖b - b'‖ < 1) (h : 1 ≤ ‖a' - b'‖) : a ≠ b := by
  rintro rfl
  have := sub_lt hb ha
  rw [show a - b' - (a - a') = a' - b' by ring] at this
  exact absurd this (not_lt.2 h)

private theorem corner_zero {K : Type} [Field K] (H H' u : M4 K) (hu : IsBlock u) (h02 : H 0 2 = 0) (h20 : H 2 0 = 0)
    (h02' : H' 0 2 = 0) (h20' : H' 2 0 = 0) (n1 : H 2 2 ≠ H' 0 0) (n2 : H 0 0 ≠ H' 2 2) (h : u * H = H' * u) :
    u 0 2 = 0 ∧ u 2 0 = 0 := by
  have e1 := congrFun (congrFun h 0) 2
  have e2 := congrFun (congrFun h 2) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, hu 0 1 (by decide), hu 0 3 (by decide), hu 1 2 (by decide),
    hu 3 2 (by decide), hu 2 1 (by decide), hu 2 3 (by decide), hu 1 0 (by decide), hu 3 0 (by decide), h02, h20, h02', h20'] at e1 e2
  constructor
  · have : u 0 2 * (H 2 2 - H' 0 0) = 0 := by linear_combination e1
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 n1)
  · have : u 2 0 * (H 0 0 - H' 2 2) = 0 := by linear_combination e2
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 n2)

private theorem gsp_of_conj {K H : Type} [Field K] [Group H] (r r' : H →* M4 K) (ν : H → K) (hν : ∀ g, ν g ≠ 0)
    (hr : ∀ g, IsGSp (ν g) (r g)) (hr' : ∀ g, IsGSp (ν g) (r' g)) (hI : Irr r) (u : M4 K) (h : ∀ g, u * r g = r' g * u) :
    ∃ a, IsGSp a u := by
  obtain ⟨gm, -, -, -, -, -, gi, -⟩ := grp K
  have c1 : ∀ g, r g * (adj u * u) = (adj u * u) * r g := by
    intro g
    have a1 : adj (r g⁻¹) = ν g⁻¹ • r g := gi _ _ _ (hr _) (by rw [← map_mul, inv_mul_cancel, map_one])
    have a2 : adj (r' g⁻¹) = ν g⁻¹ • r' g := gi _ _ _ (hr' _) (by rw [← map_mul, inv_mul_cancel, map_one])
    have a3 := congrArg adj (h g⁻¹)
    rw [gm, gm, a1, a2, smul_mul_assoc, mul_smul_comm] at a3
    have a4 := smul_right_injective _ (hν g⁻¹) a3
    rw [← mul_assoc, a4, mul_assoc, ← h, mul_assoc]
  have c2 : ∀ Y : M4 K, Y * (adj u * u) = (adj u * u) * Y := by
    intro Y
    have hY : Y ∈ Submodule.span K (Set.range r) := by rw [hI]; trivial
    induction hY using Submodule.span_induction with
    | mem x hx => obtain ⟨g, rfl⟩ := hx; exact c1 g
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul a x _ hx => rw [smul_mul_assoc, mul_smul_comm, hx]
  obtain ⟨a, ha⟩ := (Matrix.mem_range_scalar_iff_commute_single' (M := adj u * u)).2 fun i j => c2 _
  refine ⟨a, ?_⟩
  rw [IsGSp, ← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private theorem torus_of_gsp {K : Type} [Field K] (u : (M4 K)ˣ) (a : K) (hg : IsGSp a (u : M4 K)) (hu : IsBlock (u : M4 K))
    (h02 : (u : M4 K) 0 2 = 0) (h20 : (u : M4 K) 2 0 = 0) :
    ∃ t : Kˣ × Kˣ, ∀ X X' : M4 K, u * X = X' * u → X' = tconj t X := by
  have z01 := hu 0 1 (by decide)
  have z03 := hu 0 3 (by decide)
  have z12 := hu 1 2 (by decide)
  have z32 := hu 3 2 (by decide)
  have z21 := hu 2 1 (by decide)
  have z23 := hu 2 3 (by decide)
  have z10 := hu 1 0 (by decide)
  have z30 := hu 3 0 (by decide)
  have row : ∀ i, (∀ j, j ≠ i → (u : M4 K) i j = 0) → (u : M4 K) i i ≠ 0 := by
    intro i hi h0
    have := congrFun (congrFun u.mul_inv i) i
    rw [Matrix.mul_apply, Finset.sum_eq_zero, Matrix.one_apply_eq] at this
    · exact zero_ne_one this
    · intro j _
      by_cases hj : j = i
      · rw [hj, h0, zero_mul]
      · rw [hi j hj, zero_mul]
  have n0 := row 0 (by intro j hj; fin_cases j <;> simp_all)
  have n2 := row 2 (by intro j hj; fin_cases j <;> simp_all)
  have e02 := congrFun (congrFun hg 0) 2
  have e20 := congrFun (congrFun hg 2) 0
  have e00 := congrFun (congrFun hg 0) 0
  have e22 := congrFun (congrFun hg 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, z01, z03, z12, z32, z21, z23, z10, z30, h02, h20, n0, n2]
    at e02 e20 e00 e22
  have n1 := row 1 (by intro j hj; fin_cases j <;> simp_all)
  have n3 := row 3 (by intro j hj; fin_cases j <;> simp_all)
  have hd : (u : M4 K) = Matrix.diagonal fun i => (u : M4 K) i i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [z01, z03, z12, z32, z21, z23, z10, z30, h02, h20, e02, e20]
  refine ⟨(Units.mk0 _ (div_ne_zero n2 n3), Units.mk0 _ (div_ne_zero n1 n3)), fun X X' h => ?_⟩
  have hw : ∀ i j, (wv (Units.mk0 _ (div_ne_zero n2 n3), Units.mk0 _ (div_ne_zero n1 n3)) (wt i j) : K) * (u : M4 K) j j =
      (u : M4 K) i i := by
    have e0 : (u : M4 K) 0 0 = (u : M4 K) 1 1 * (u : M4 K) 2 2 / (u : M4 K) 3 3 := by
      field_simp; linear_combination e00 - e22
    intro i j
    fin_cases i <;> fin_cases j <;> simp [wv, wt, lamW, muW, e0] <;> field_simp
  have hn : ∀ j, (u : M4 K) j j ≠ 0 := by intro j; fin_cases j <;> assumption
  ext i j
  have := congrFun (congrFun h i) j
  rw [hd, Matrix.diagonal_mul, Matrix.mul_diagonal] at this
  apply mul_right_cancel₀ (hn j)
  rw [← this, tconj, Matrix.of_apply, ← hw i j]
  ring

private theorem norm_le_one_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem norm_unit {l : ℕ} [Fact l.Prime] (c : Coef l) {x : c.O} (hx : IsUnit x) :
    ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := by
  have hle : ∀ y : c.O, ‖(y : PadicAlgCl l)‖ ≤ 1 := fun y =>
    norm_le_one_int l _ ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) y).map c.O.val)
  obtain ⟨u, rfl⟩ := hx
  show ‖((u : c.O) : PadicAlgCl l)‖ = 1
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖((u⁻¹ : c.Oˣ) : c.O).1‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := hle u
  have h3 := hle (u⁻¹ : c.Oˣ)
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  nlinarith

private theorem norm_sub_of_res {l : ℕ} [Fact l.Prime] (c : Coef l) {x y : c.O} (h : residue c.O x ≠ residue c.O y) :
    ‖algebraMap c.O (PadicAlgCl l) x - algebraMap c.O (PadicAlgCl l) y‖ = 1 := by
  rw [← map_sub]
  refine norm_unit c ?_
  rw [← residue_ne_zero_iff_isUnit, map_sub]
  exact sub_ne_zero.2 h

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.conjTorus :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r r', D.EPt r → D.EPt r' → Irr r → IsConj4 r r' → ∃ t, ∀ g, r' g = tconj t (r g) := by
  intro Ω _ _ _ l _ c D hD r r' hr hr' hI ⟨u, hu⟩
  have hint : ∀ g, (u : M4 (PadicAlgCl l)) * r g = r' g * u := fun g => by
    rw [hu g, Units.inv_mul_cancel_right]
  obtain ⟨hM, -, hN, -⟩ := ptIn D hD _ r hr
  obtain ⟨hM', -, hN', -⟩ := ptIn D hD _ r' hr'
  obtain ⟨-, hc, -⟩ := eptInt D hD r hr
  obtain ⟨-, hc', -⟩ := eptInt D hD r' hr'
  obtain ⟨-, hT, -, -, -, -, -, -, -, hph, -⟩ := facts D hD
  have hdiag : ∀ g, D.r0E g = Matrix.diagonal fun i => algebraMap c.O (PadicAlgCl l) (D.ps i g : c.O) := fun g => by
    ext i j
    show algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) = _
    by_cases h : i = j
    · subst h; rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
  have hbar : ∀ g i, D.rbar g i i = Raw.bar (D.ps i) g := fun g i => by
    show residue c.O (Matrix.diagonal (fun i => (D.ps i g : c.O)) i i) = _
    rw [Matrix.diagonal_apply_eq]
  have hB : IsBlock (u : M4 (PadicAlgCl l)) := by
    refine block_of_intertwine (r D.ph) (r' D.ph) u _ (fun i j => hdiag D.ph ▸ hc _ i j) (fun i j => hdiag D.ph ▸ hc' _ i j)
      hN.1 hN'.1 (fun i j hij => (norm_sub_of_res c ?_).ge) (hint _)
    have := (hT l (Finset.mem_insert_self _ _)).2.2 i j hij
    rw [← hbar, ← hbar, ← hph, hbar, hbar] at this
    exact this
  have hth : ∀ g, ‖algebraMap c.O (PadicAlgCl l) (D.th g : c.O)‖ = 1 := fun g => norm_unit c (Units.isUnit _)
  have hH : ∀ s : G ℚ Ω →* M4 (PadicAlgCl l), (∀ g i j, ‖s g i j - D.r0E g i j‖ < 1) → ∀ i,
      ‖D.hEl s i i - algebraMap c.O (PadicAlgCl l) ((D.ps i D.g0 : c.O) + (D.th D.g0 : c.O) * (D.ps i D.g0⁻¹ : c.O))‖ < 1 := by
    intro s hs i
    have h1 := hs D.g0 i i
    have h2 := hs D.g0⁻¹ i i
    rw [hdiag, Matrix.diagonal_apply_eq] at h1 h2
    have h3 : ‖algebraMap c.O (PadicAlgCl l) (D.th D.g0 : c.O) *
        (s D.g0⁻¹ i i - algebraMap c.O (PadicAlgCl l) (D.ps i D.g0⁻¹ : c.O))‖ < 1 := by
      rw [norm_mul, hth, one_mul]; exact h2
    convert add_lt h1 h3 using 2
    rw [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
    ring
  have hne : residue c.O ((D.ps 0 D.g0 : c.O) + (D.th D.g0 : c.O) * (D.ps 0 D.g0⁻¹ : c.O)) ≠
      residue c.O ((D.ps 2 D.g0 : c.O) + (D.th D.g0 : c.O) * (D.ps 2 D.g0⁻¹ : c.O)) := by
    have p0 : D.ps 0 = D.th := rfl
    have p2 : D.ps 2 = D.al := rfl
    have q0 : (D.th D.g0 : c.O) * (D.th D.g0⁻¹ : c.O) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    have q1 : (D.th D.g0 : c.O) = (D.al D.g0 : c.O) * (D.Psi D.g0 : c.O) := rfl
    have q2 : (D.al D.g0 : c.O) * (D.al D.g0⁻¹ : c.O) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    rw [p0, p2, q0, q1, mul_right_comm, q2, one_mul, map_add, map_add, map_mul, map_one]
    intro h
    have : (Raw.bar D.al D.g0 - 1) * (Raw.bar D.Psi D.g0 - 1) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).elim (sub_ne_zero.2 hD.genElt_alpha) (sub_ne_zero.2 hD.genElt_Psi)
  obtain ⟨h02, h20⟩ := corner_zero (D.hEl r) (D.hEl r') u hB hN.2.1 hN.2.2 hN'.2.1 hN'.2.2
    (ne_of_close (hH r hc 2) (hH r' hc' 0) (norm_sub_of_res c hne.symm).ge)
    (ne_of_close (hH r hc 0) (hH r' hc' 2) (norm_sub_of_res c hne).ge)
    (by rw [Raw.hEl, Raw.hEl, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hint, hint])
  obtain ⟨a, ha⟩ := gsp_of_conj r r' _ (fun g => norm_ne_zero_iff.1 (by rw [hth g]; exact one_ne_zero)) hM hM' hI u hint
  obtain ⟨t, ht⟩ := torus_of_gsp u a ha hB h02 h20
  exact ⟨t, fun g => ht _ _ (hint g)⟩
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Gen

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

private theorem algHom_ext_graded {ξ ξ' : A →ₐ[O] K} (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  ext f
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous f => exact h _ _ f.2
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem same_orbit_trans {ξ ξ' ξ'' : A →ₐ[O] K} (h : SameOrbit 𝒜 ξ ξ') (h' : SameOrbit 𝒜 ξ' ξ'') :
    SameOrbit 𝒜 ξ ξ'' := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨t, rfl⟩ := h'
  refine ⟨t * s, algHom_ext_graded 𝒜 fun j f hf => ?_⟩
  simp only [act_of_mem 𝒜 _ _ hf, zpowersHom_apply, toAdd_ofAdd, mul_zpow, Units.val_mul, mul_assoc]

private theorem exists_minimal_orbit_cover (I : Ideal A) (h : ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T) :
    ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ ∀ ξ ∈ T, ∀ ξ' ∈ T, SameOrbit 𝒜 ξ ξ' → ξ = ξ' := by
  classical
  have h' : ∃ n, ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ T.card = n := by
    obtain ⟨T, hT⟩ := h
    exact ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, hc⟩ := Nat.find_spec h'
  refine ⟨T, hT, fun ξ hξ ξ' hξ' ho => ?_⟩
  by_contra hne
  refine Nat.find_min h' (m := (T.erase ξ').card) (hc ▸ Finset.card_erase_lt_of_mem hξ') ⟨T.erase ξ', ⟨?_, ?_⟩, rfl⟩
  · exact fun x hx => hT.1 x (Finset.mem_of_mem_erase hx)
  · intro x hx h2
    obtain ⟨y, hy, hyx⟩ := hT.2 x hx h2
    by_cases e : y = ξ'
    · subst e
      exact ⟨ξ, Finset.mem_erase.2 ⟨hne, hξ⟩, same_orbit_trans 𝒜 ho hyx⟩
    · exact ⟨y, Finset.mem_erase.2 ⟨e, hy⟩, hyx⟩

end Gen

private theorem torus_conj_mul {R : Type} [CommRing R] (s t : Rˣ × Rˣ) (X : M4 R) :
    tconj s (tconj t X) = tconj (s * t) X := by
  ext i j
  simp only [tconj, wv, Matrix.of_apply, Prod.fst_mul, Prod.snd_mul, mul_zpow, Units.val_mul]
  ring

private theorem torus_conj_one {R : Type} [CommRing R] (X : M4 R) : tconj 1 X = X := by
  ext i j
  simp [tconj, wv]

private theorem irreducible_torus_conjugate {R H : Type} [CommRing R] [Group H] (t : Rˣ × Rˣ) (r r' : H →* M4 R)
    (h : ∀ g, r' g = tconj t (r g)) (hr : Irr r) : Irr r' := by
  obtain ⟨u, hu⟩ := (grp R).2.2.2.2.2.2.2.2.2.2.2.2 t
  have key : ∀ X ∈ Submodule.span R (Set.range r), (u : M4 R) * X * (u⁻¹ : (M4 R)ˣ) ∈ Submodule.span R (Set.range r') := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, by rw [h, hu]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx
  refine eq_top_iff.2 fun X _ => ?_
  have := key (((u⁻¹ : (M4 R)ˣ) : M4 R) * X * u) (by rw [show Submodule.span R (Set.range r) = ⊤ from hr]; trivial)
  simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using this

private theorem real_ratio_bound (s n e L S : ℝ) (he : 0 < e) (hL : 0 < L) (h1 : s ≤ n) (h2 : n ≤ 2 * (S * e / L)) :
    s / e * L ≤ 2 * S := by
  have h3 : s * L ≤ 2 * S * e := by
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hL.le
    have e1 : 2 * (S * e / L) * L = 2 * S * e := by field_simp
    rwa [e1] at this
  rw [div_mul_eq_mul_div, div_le_iff₀ he]
  exact h3

section Pts

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

private theorem same_orbit_of_conjugate_reps (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (h0 : D.Fin0)
    (ξ ξ' : M.SS →ₐ[c.O] PadicAlgCl l) (t t' : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ) (r r' : G ℚ Ω →* M4 (PadicAlgCl l))
    (he : D.EPt r) (he' : D.EPt r') (hi : Irr r) (ht : ∀ g, r g = tconj t (M.rep ξ g))
    (ht' : ∀ g, r' g = tconj t' (M.rep ξ' g)) (hc : IsConj4 r r') :
    SameOrbit M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) := by
  obtain ⟨s, hs⟩ := conjTorus D hD _ _ he he' hi hc
  obtain ⟨η, hη, hw⟩ := ptAct D hD M _ ξ (t'⁻¹ * (s * t))
  have e : η = ξ' := by
    refine ptExt D hD M h0 _ _ _ (MonoidHom.ext fun g => ?_)
    rw [hη, ← torus_conj_mul, ← torus_conj_mul, ← ht, ← hs, ht', torus_conj_mul, inv_mul_cancel, torus_conj_one]
  subst e
  refine ⟨(t'⁻¹ * (s * t)).2, algHom_ext_graded M.gr fun j f hf => ?_⟩
  rw [act_of_mem M.gr _ _ hf, AlgHom.comp_apply, AlgHom.comp_apply, hw (0, j) _ ((kerA D hD M).2.2 j f hf)]
  simp only [wv, zpow_zero, one_mul, zpowersHom_apply, toAdd_ofAdd]

private theorem exists_rep_family_from_points (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hV : SoV Ω l)
    (h0 : D.Fin0) (hNE : D.NoEnd) (g : G ℚ Ω) (a : M.A)
    (ha : ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ)) :
    ∃ ρ : (M.A →ₐ[c.O] PadicAlgCl l) → (G ℚ Ω →* M4 (PadicAlgCl l)),
      (∀ x, OnS M.eqns.ideal x ∧ TwoSigned M.gr x → (D.EPt (ρ x) ∧ Irr (ρ x)) ∧ D.aVal g (ρ x) = x a) ∧
      ∀ x x', OnS M.eqns.ideal x ∧ TwoSigned M.gr x → OnS M.eqns.ideal x' ∧ TwoSigned M.gr x' →
        IsConj4 (ρ x) (ρ x') → SameOrbit M.gr x x' := by
  have hpt : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, ∃ r : G ℚ Ω →* M4 (PadicAlgCl l), OnS M.eqns.ideal x ∧ TwoSigned M.gr x →
      ((D.EPt r ∧ Irr r) ∧ D.aVal g r = x a) ∧ ∃ (ξ : M.SS →ₐ[c.O] PadicAlgCl l)
        (t : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ), ξ.comp M.toSS = x ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
    intro x
    by_cases hx : OnS M.eqns.ideal x
    · obtain ⟨ξ, hξ⟩ := ptLift D hD M x hx
      obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M h0 ξ
      refine ⟨r, fun h2 => ⟨⟨⟨hr, irreducible_torus_conjugate t _ _ hrt (twoIrr D hD M hL hV h0 hNE ξ (by rw [hξ]; exact h2.2))⟩, ?_⟩,
        ξ, t, hξ, hrt⟩⟩
      rw [← hξ, AlgHom.comp_apply, ha, Raw.aVal, Raw.aVal, hrt, (grp _).2.2.2.2.2.2.2.2.2.2.2.1]
    · exact ⟨1, fun h => absurd h.1 hx⟩
  choose ρ hρ using hpt
  refine ⟨ρ, fun x hx => (hρ x hx).1, fun x x' hx hx' hc => ?_⟩
  obtain ⟨⟨⟨he, hi⟩, -⟩, ξ, t, hξ, ht⟩ := hρ x hx
  obtain ⟨⟨⟨he', -⟩, -⟩, ξ', t', hξ', ht'⟩ := hρ x' hx'
  have := same_orbit_of_conjugate_reps hD M h0 ξ ξ' t t' _ _ he he' hi ht ht' hc
  rwa [hξ, hξ'] at this

private theorem covers_and_cotangent_length_bounds (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hM : LemmaM) (hL : Loc.LocalPublishedTheorems) (hV : SoV Ω l)
    (h0 : D.Fin0) (hNE : D.NoEnd) (hR : D.AllIrr D.RigidAt) (a : M.A) (h5 : M5 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal a) :
    (∃ T : Finset (M.A →ₐ[c.O] PadicAlgCl l), Covers M.gr M.eqns.ideal T) ∧ cotLen M.x0 M.gr (-1) M.eqns.F ≠ ⊤ ∧
    ∀ T : Finset (M.A →ₐ[c.O] PadicAlgCl l), Covers M.gr M.eqns.ideal T → ((cotLen M.x0 M.gr (-1) M.eqns.F).toNat : ℝ) ≤
      2 * ∑ ξ ∈ T, -Real.log ‖ξ a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  obtain ⟨h1, h2, h3⟩ := m1b D hD M hV
  exact hM c.O (PadicAlgCl l) _ (nval c) M.A M.gr M.x0 (aW D hD M) _ _ _ _ _ M.eqns a
    ⟨M.one_le, aSmooth D hD M, h1, h2, h3⟩ (m2 D hD M h0) (m3 D hD M hL hV h0) (m4 D hD M hL hV h0 hNE hR) h5

end Pts

theorem UpperTheory.V.GradeZeroInterpolatingElement.galoisRep_ineq_of_allIrreducible_nonvanishing :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, LemmaM → LemmaM' → Loc.LocalPublishedTheorems → SoV Ω l → SoFin Ω l → D.Fin0 → D.NoEnd → D.AllIrr D.RigidAt → ∀ g, D.AllIrr (fun r => D.aVal g r ≠ 0) → D.Ineq g := by
  intro Ω _ _ _ l hl c D hD M hM hM' hL hV hF h0 hNE hR g hA
  classical
  obtain ⟨inst⟩ := aGraded D hD M
  obtain ⟨a, ha0, hax, ha⟩ := aElt D hD M g
  obtain ⟨ρ, hρ, horb⟩ := exists_rep_family_from_points hD M hL hV h0 hNE g a ha
  obtain ⟨hT, hfin, hle⟩ := covers_and_cotangent_length_bounds hD M hM hL hV h0 hNE hR a
    ⟨ha0, hax, fun x hx h2 => by
      obtain ⟨⟨he, hi⟩, hv⟩ := hρ x ⟨hx, h2⟩
      rw [← hv]
      exact hA _ he hi⟩
  obtain ⟨T, hT, hmin⟩ := exists_minimal_orbit_cover M.gr _ hT
  have hinj : ∀ x ∈ T, ∀ x' ∈ T, IsConj4 (ρ x) (ρ x') → x = x' := fun x hx x' hx' hc =>
    hmin x hx x' hx' (horb x x' (hT.1 x hx) (hT.1 x' hx') hc)
  refine ⟨(shaCoc D hD hF).1, T.image ρ, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    exact (hρ x (hT.1 x hx)).1
  · intro r hr r' hr' hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hr'
    rw [hinj x hx x' hx' hc]
  · have e2 : ∑ r ∈ T.image ρ, -Real.log ‖D.aVal g r‖ = ∑ x ∈ T, -Real.log ‖x a‖ := by
      rw [Finset.sum_image fun x hx x' hx' e => hinj x hx x' hx' ⟨1, fun g => by
        rw [e, inv_one, Units.val_one, one_mul, mul_one]⟩]
      exact Finset.sum_congr rfl fun x hx => by rw [(hρ x (hT.1 x hx)).2]
    rw [e2]
    have hs := hle T hT
    rw [← Finset.sum_div, ← Finset.sum_mul] at hs
    obtain ⟨-, -, -, -, -, e0, e1, -⟩ := dvrFacts l c.O
    have he : 0 < (eO l c.O).toNat :=
      ENat.toNat_pos e0 (ne_top_of_le_ne_top (ENat.coe_ne_top _) e1)
    exact real_ratio_bound _ _ _ _ _ (Nat.cast_pos.2 he) (Real.log_pos (by exact_mod_cast hl.out.one_lt))
      (Nat.cast_le.2 (ENat.toNat_le_toNat (mPrime D hD M hM' hF) hfin)) hs
end
