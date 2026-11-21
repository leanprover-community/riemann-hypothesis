import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEtaCharacterImaginaryQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EulerProductInductionSupported
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteOrderHeckeCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.GlobTw
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PolFacts
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.Loc2
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.RsOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.EulOf
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanEqTopOfIrreducibleOverAlgClosed
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence

section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unr_mul {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) : IsUnram (a * b) := fun x hx => by
  rw [MonoidHom.mul_apply, ha x hx, hb x hx, one_mul]

private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]

private theorem unr_mul_iff {a μ : kˣ →* ℂˣ} (hμ : IsUnram μ) : IsUnram (a * μ) ↔ IsUnram a :=
  ⟨fun h => by simpa using unr_mul h (unr_inv hμ), fun h => unr_mul h hμ⟩

private theorem lin_shift (ξ μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    lin (ξ * μ) = (lin ξ).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  unfold lin
  by_cases h : IsUnram ξ
  · rw [if_pos ((unr_mul_iff hμ).2 h), if_pos h]
    simp [MonoidHom.mul_apply, mul_assoc]
  · rw [if_neg (fun h' => h ((unr_mul_iff hμ).1 h')), if_neg h]
    simp

private theorem linear_factor_unramified_twist (ν c μ : kˣ →* ℂˣ) (hμ : IsUnram μ) :
    lin3 ν (c * μ) = (lin3 ν c).comp (C ((μ (unif k) : ℂˣ) : ℂ) * X) := by
  unfold lin3
  rw [← mul_assoc ν, ← mul_assoc ν⁻¹, lin_shift _ _ hμ, lin_shift _ _ hμ, lin_shift _ _ hμ]
  simp [mul_comp]

end Loc

private theorem pol_shift (h1 : PolFacts) (h2 : NormVal) (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ))
    (w : PlacesOver K v) (s : Multiset (IrrGL (w.1.adicCompletion K))) (θ μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsUnram μ) :
    (pol s ((θ * μ).comp (nm w))).comp (X ^ fdeg w) =
      ((pol s (θ.comp (nm w))).comp (X ^ fdeg w)).comp (C ((μ (unif (v.adicCompletion ℚ)) : ℂˣ) : ℂ) * X) := by
  obtain ⟨hu, he⟩ := (h2 ℚ K v w μ).1 hμ
  have e1 : (θ * μ).comp (nm w) = θ.comp (nm w) * μ.comp (nm w) := rfl
  have e2 := ((h1 (w.1.adicCompletion K)).2.2.2 s (θ.comp (nm w))).2.2.2 (μ.comp (nm w)) hu
  rw [e1, e2, comp_assoc, comp_assoc]
  congr 1
  simp only [MonoidHom.comp_apply, he, Units.val_pow_eq_pow_val, X_pow_comp, mul_comp, C_comp, X_comp, mul_pow, C_pow,
    Polynomial.pow_comp]

private theorem unr_comp (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 ℚ)) (w : PlacesOver K v)
    (μ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hμ : IsUnram μ) : IsUnram (μ.comp (nm w)) := (normVal ℚ K v w μ).1 hμ |>.1

private theorem loc_mul (c η : HeckeCharacter ℚ) (u : Ad3.Pl) : localChar (c * η) u = localChar c u * (toH η).loc u :=
  MonoidHom.ext fun x => Units.ext (by
    rw [MonoidHom.mul_apply, Units.val_mul, Ad3P.DihedralUnramifiedPlaces.loc_eq, GroundTheory.Automorphic.GodementSection.coe_localChar,
      GroundTheory.Automorphic.GodementSection.coe_localChar, GroundTheory.Automorphic.GodementSection.coe_localChar,
      HeckeCharacter.localComponent_apply, HeckeCharacter.localComponent_apply, HeckeCharacter.localComponent_apply]
    rfl)

private theorem step (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (D : Ad3.Dat)
    (hAn : Ad3.An D) (P : CuspSub K 3) (hSys : AdSys D P) (η : HeckeCharacter ℚ) (hη : EtaOK K η) (v : HeightOneSpectrum (𝓞 ℚ))
    (s' : ∀ w : PlacesOver K v, Multiset (IrrGL (w.1.adicCompletion K))) (hs' : ∀ w, SuppAt P w.1 (s' w))
    (θ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hθ : IsSmoothChar θ) :
    ∏ j ∈ Finset.range 2, lin (D.ν v * (θ * ((toH η) ^ j).loc v)) * lin (θ * ((toH η) ^ j).loc v) *
        lin ((D.ν v)⁻¹ * (θ * ((toH η) ^ j).loc v)) =
      ∏ w, (pol (s' w) (θ.comp (nm w))).comp (X ^ fdeg w) := by
  have hF := suppFacts K 3 (by norm_num) P
  choose s hs using fun w => (hF w).1
  have hR : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K :=
    (Finset.finite_toSet _).compl_mem_cofinite
  have hE : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ≠ v ∧ u ∉ D.bad ∧ (toH η).UnrAt u ∧ ∀ w : PlacesOver K u,
      IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧ Fintype.card (PlacesOver K u) * fdeg w = 2 ∧
        w.1 ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∧
        (CG.mk P).HasSat w.1 {D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w, 1, (D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w)⁻¹} := by
    have h1 : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ≠ v := (Set.finite_singleton v).compl_mem_cofinite
    have h3 : ∀ᶠ u : Ad3.Pl in Filter.cofinite, u ∉ D.bad := (Finset.finite_toSet _).compl_mem_cofinite
    filter_upwards [hη.ae, hSys, IdeleNorm.eventually_forall_placesOver ℚ hR, h1, h3] with u a b c d e
    exact ⟨d, e, a.1, fun w => ⟨(a.2 w).1, (a.2 w).2, c w, b w⟩⟩
  set S₀ : Finset Ad3.Pl := (Filter.eventually_cofinite.1 hE).toFinset with hS₀
  have hgood : ∀ u ∉ S₀, _ := fun u hu => by
    simpa only [hS₀, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hu
  have hv : v ∈ S₀ := by
    by_contra h
    exact (hgood v h).1 rfl
  have hbad : D.bad ⊆ S₀ := fun u hu => by
    by_contra h
    exact (hgood u h).2.1 hu
  let bad : ∀ u : Ad3.Pl, Finset ((u.adicCompletion ℚ)ˣ →* ℂˣ) := fun u =>
    {D.ν u, 1, (D.ν u)⁻¹, D.ν u * (toH η).loc u, (toH η).loc u, (D.ν u)⁻¹ * (toH η).loc u}
  let bad' : ∀ w : HeightOneSpectrum (𝓞 K), Finset ((w.adicCompletion K)ˣ →* ℂˣ) := fun w =>
    (s w).toFinset.image fun y => if h : ∃ ξ hξ, y = IrrGL.ofChar ξ hξ then h.choose else 1
  have hbad' : ∀ w, ∀ ζ ∈ chars (s w), ζ ∈ bad' w := by
    rintro w ζ ⟨hζ, hm⟩
    refine Finset.mem_image.2 ⟨_, Multiset.mem_toFinset.2 hm, ?_⟩
    have h : ∃ ξ hξ, IrrGL.ofChar ζ hζ = IrrGL.ofChar ξ hξ := ⟨ζ, hζ, rfl⟩
    rw [dif_pos h]
    obtain ⟨hξ, e⟩ := h.choose_spec
    exact ((polFacts _).2.2.1 _ _ _ _ e).symm
  obtain ⟨χ, hχv, hχ⟩ := globTw ℚ K v θ hθ S₀ bad bad'
  obtain ⟨c, hc, hcu⟩ := UpperTheory.exists_finite_order_hecke_character χ
  have key : ∀ (u : Ad3.Pl) (ξ : (u.adicCompletion ℚ)ˣ →* ℂˣ), ¬ IsUnram (ξ * χ.loc u) → ¬ IsUnram (ξ * localChar c u) :=
    fun u ξ h h' => h (by
      have := unr_mul h' (hcu u)
      rwa [mul_comm (χ.loc u), ← mul_assoc, mul_assoc ξ, mul_inv_cancel, mul_one] at this)
  have hdeep : ∀ u ∈ S₀, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u) ∧
      ∀ w : PlacesOver K u, ∀ ζ ∈ chars (s w.1), ¬ IsUnram (ζ * (localChar c u).comp (nm w)) := by
    intro u hu hne
    obtain ⟨h1, h3⟩ := hχ u hu hne
    have hb := fun ξ (hξ : ξ ∈ bad u) => key u ξ (h1 ξ hξ)
    rw [loc_mul]
    refine ⟨⟨hb _ (by simp [bad]), by simpa using hb 1 (by simp [bad]), hb _ (by simp [bad])⟩,
      ⟨?_, ?_, ?_⟩, fun w ζ hζ h' => h3 w ζ (hbad' _ _ hζ) ?_⟩
    · have := hb (D.ν u * (toH η).loc u) (by simp [bad])
      rwa [mul_assoc, mul_comm ((toH η).loc u)] at this
    · have := hb ((toH η).loc u) (by simp [bad])
      rwa [mul_comm] at this
    · have := hb ((D.ν u)⁻¹ * (toH η).loc u) (by simp [bad])
      rwa [mul_assoc, mul_comm ((toH η).loc u)] at this
    · have := unr_mul h' (unr_comp K u w _ (hcu u))
      have e : (χ.loc u).comp (nm w) = (localChar c u).comp (nm w) * (χ.loc u * (localChar c u)⁻¹).comp (nm w) := by
        ext x
        simp
      rwa [mul_assoc, ← e] at this
  have core := UpperTheory.euler_product_induction_supported K h2 D hAn P η c hη hc S₀ v s hs hbad hv (fun u hu => (hgood u hu).2.2) hdeep
  set θc := localChar c v with hθc
  have hμ : IsUnram (θ * θc⁻¹) := by
    have := unr_mul (unr_inv hχv) (hcu v)
    have e : (χ.loc v * θ⁻¹)⁻¹ * (χ.loc v * (localChar c v)⁻¹) = θ * θc⁻¹ := by
      rw [mul_inv, inv_inv, mul_comm (χ.loc v)⁻¹, mul_assoc, inv_mul_cancel_left]
    rwa [e] at this
  set μ := θ * θc⁻¹ with hμd
  have eθ : θ = θc * μ := by rw [hμd, mul_comm θ, mul_inv_cancel_left]
  have e0 : s' = fun w : PlacesOver K v => s w.1 := funext fun w => (hF w.1).2.1 _ _ (hs' w) (hs w.1)
  subst e0
  have l0 : ((toH η) ^ 0).loc v = 1 := by rw [pow_zero]; rfl
  have e2 : θ * (toH η).loc v = localChar (c * η) v * μ := by
    rw [loc_mul, ← hθc]
    exact (congrArg (· * (toH η).loc v) eθ).trans (mul_right_comm _ _ _)
  have e3 : ∏ j ∈ Finset.range 2, lin (D.ν v * (θ * ((toH η) ^ j).loc v)) * lin (θ * ((toH η) ^ j).loc v) *
        lin ((D.ν v)⁻¹ * (θ * ((toH η) ^ j).loc v)) = lin3 (D.ν v) θ * lin3 (D.ν v) (θ * (toH η).loc v) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, l0, mul_one, pow_one, lin3]
  rw [e3, e2, linear_factor_unramified_twist _ _ _ hμ]
  conv_lhs => rw [eθ, linear_factor_unramified_twist _ _ _ hμ]
  rw [← mul_comp, core, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  conv_rhs => rw [eθ]
  rw [pol_shift polFacts normVal K v w _ _ _ hμ]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.matchAd :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.MatchAd := by
  intro K _ _ _ h2 D hAn P hSys
  obtain ⟨η, hη⟩ := UpperTheory.exists_eta_character_imaginary_quadratic K h2
  exact ⟨toH η, fun v => ⟨fun w => (hη.loc v w).1, fun θ hθ w hw => ((hη.loc v w).2.2 θ hθ).2.2 (by
    rw [h2] at *; exact hw), fun s' hs' θ hθ => step K h2 D hAn P hSys η hη v s' hs' θ hθ⟩⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

private theorem sum_card_le {α ι : Type*} [Fintype ι] (Q : ι → α → Prop) (hQ : ∀ c c' y, Q c y → Q c' y → c = c')
    (s : Multiset α) : ∑ c, (s.filter (Q c)).card ≤ (s.filter fun y => ∃ c, Q c y).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons y s ih =>
    simp only [Multiset.filter_cons, Multiset.card_add, Finset.sum_add_distrib]
    refine add_le_add ?_ ih
    by_cases h : ∃ c, Q c y
    · obtain ⟨c, hc⟩ := h
      rw [if_pos ⟨c, hc⟩, Finset.sum_eq_single c (fun b _ hb => by rw [if_neg fun h => hb (hQ _ _ _ h hc)]; rfl) (by simp),
        if_pos hc]
    · rw [if_neg h, Finset.sum_eq_zero fun b _ => by rw [if_neg fun h' => h ⟨b, h'⟩]; rfl]
      exact Nat.zero_le _

private theorem comb {W : Type} [Fintype W] {α : W → Type 1} (r : Setoid (Fin 3)) (s : ∀ w, Multiset (α w))
    (Q : ∀ w, Fin 3 → α w → Prop) (f : W → ℕ) (hf : ∀ w, 0 < f w) (hs : ∀ w, (s w).card ≤ 3)
    (hQ : ∀ w i i' y, Q w i y → Q w i' y → r i i')
    (h : ∀ i, (Finset.univ.filter fun i' => r i' i).card * ∑ w, f w = ∑ w, f w * ((s w).filter (Q w i)).card) :
    ∀ w, ∀ y ∈ s w, ∃ i, Q w i y := by
  have h3 : ∑ c : Quotient r, (Finset.univ.filter fun i' => r i' c.out).card = 3 := by
    have := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := Quotient.mk r) (by simp)
    rw [Finset.card_univ, Fintype.card_fin] at this
    refine (Finset.sum_congr rfl fun c _ => congrArg _ (Finset.filter_congr fun i _ => ?_)).trans this.symm
    exact Quotient.mk_eq_iff_out.symm
  have hle : ∀ w, ∑ c : Quotient r, ((s w).filter (Q w c.out)).card ≤ ((s w).filter fun y => ∃ c : Quotient r, Q w c.out y).card :=
    fun w => sum_card_le (fun c : Quotient r => Q w c.out)
      (fun c c' y h h' => by rw [← c.out_eq, ← c'.out_eq]; exact Quotient.sound (hQ w _ _ y h h')) (s w)
  have hle3 : ∀ w, ∑ c : Quotient r, ((s w).filter (Q w c.out)).card ≤ 3 := fun w =>
    (hle w).trans ((Multiset.card_le_card (Multiset.filter_le _ _)).trans (hs w))
  have heq : ∑ w, f w * ∑ c : Quotient r, ((s w).filter (Q w c.out)).card = ∑ w, f w * 3 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_congr rfl fun (c : Quotient r) _ => h c.out, ← Finset.sum_mul, h3, ← Finset.sum_mul,
      mul_comm]
  intro w y hy
  have h1 := (Finset.sum_eq_sum_iff_of_le fun w _ => Nat.mul_le_mul_left (f w) (hle3 w)).1 heq w (Finset.mem_univ w)
  have h2 := Nat.eq_of_mul_eq_mul_left (hf w) h1
  have h4 := Multiset.eq_of_le_of_card_le (Multiset.filter_le (fun y => ∃ c : Quotient r, Q w c.out y) (s w))
    ((hs w).trans (h2.symm.le.trans (hle w)))
  obtain ⟨c, hc⟩ := Multiset.filter_eq_self.1 h4 y hy
  exact ⟨_, hc⟩

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem un_div {a b c : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) (h : c = a * b⁻¹) : IsUnram c := fun x hx => by
  simp [h, ha x hx, hb x hx]

private theorem lin_ne (ξ : kˣ →* ℂˣ) : lin ξ ≠ 0 := by
  intro h
  have := congrArg (eval 0) h
  unfold lin at this
  split_ifs at this <;> simp at this

private theorem lin_deg (ξ : kˣ →* ℂˣ) : (lin ξ).natDegree = if IsUnram ξ then 1 else 0 := by
  unfold lin
  split_ifs
  · rw [natDegree_sub_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X _ (Units.ne_zero _)]
    simp
  · simp

private theorem lin_root {ξ : kˣ →* ℂˣ} {x : ℂ} (h : (lin ξ).eval x = 0) :
    IsUnram ξ ∧ ((ξ (unif k) : ℂˣ) : ℂ) * x = 1 := by
  unfold lin at h
  split_ifs at h with hu
  · refine ⟨hu, ?_⟩
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X] at h
    exact (sub_eq_zero.1 h).symm
  · simp at h

end Loc

private theorem core {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 ℚ)}
    (a : Fin 3 → (v.adicCompletion ℚ)ˣ →* ℂˣ) (ha : ∀ i, IsSmoothChar (a i)) (e : ℕ → (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (he : ∀ j ∈ Finset.range 2, ∀ w : PlacesOver K v, (e j).comp (nm w) = 1)
    (hc : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ → ∀ w : PlacesOver K v, IsUnram (θ.comp (nm w)) →
      ((Finset.range 2).filter fun j => IsUnram (θ * e j)).card = ∑ w' : PlacesOver K v, fdeg w')
    (s : ∀ w : PlacesOver K v, Multiset (IrrGL (w.1.adicCompletion K))) (hs : ∀ w, (s w).card ≤ 3)
    (hm : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ →
      ∏ j ∈ Finset.range 2, ∏ i, lin (a i * θ * e j) = ∏ w, (pol (s w) (θ.comp (nm w))).comp (X ^ fdeg w))
    (w : PlacesOver K v) : ∀ y ∈ s w, ∃ i hζ, y = IrrGL.ofChar ((a i).comp (nm w)) hζ := by
  have hf : ∀ w : PlacesOver K v, 0 < fdeg w := fun w => (normVal ℚ K v w 1).2.2.1
  have hup : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, ∀ j ∈ Finset.range 2, ∀ w : PlacesOver K v,
      (θ * e j).comp (nm w) = θ.comp (nm w) := fun θ j hj w => by
    rw [MonoidHom.mul_comp, he j hj w, mul_one]
  have hup' : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, ∀ j ∈ Finset.range 2, IsUnram (θ * e j) → ∀ w : PlacesOver K v,
      IsUnram (θ.comp (nm w)) := fun θ j hj h w => hup θ j hj w ▸ ((normVal ℚ K v w _).1 h).1
  have hind : ∀ θ : (v.adicCompletion ℚ)ˣ →* ℂˣ, IsSmoothChar θ → ∀ w : PlacesOver K v, IsUnram (θ.comp (nm w)) →
      ∀ w' : PlacesOver K v, IsUnram (θ.comp (nm w')) := fun θ hθ w h => by
    have h1 : 0 < ((Finset.range 2).filter fun j => IsUnram (θ * e j)).card := by
      rw [hc θ hθ w h]
      exact Finset.sum_pos (fun w _ => hf w) ⟨w, Finset.mem_univ _⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 h1
    exact hup' θ j (Finset.mem_filter.1 hj).1 (Finset.mem_filter.1 hj).2
  let r : Setoid (Fin 3) := ⟨fun i i' => IsUnram ((a i * (a i')⁻¹).comp (nm w)),
    ⟨fun i x _ => by simp, fun {i i'} h x hx => by
      have := h x hx
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this ⊢
      exact this.symm, fun {i i' i''} h h' x hx => by
      have h1 := h x hx
      have h2 := h' x hx
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at h1 h2 ⊢
      exact h1.trans h2⟩⟩
  have key := comb r s (fun w i y => ∃ ξ hξ, y = IrrGL.ofChar ξ hξ ∧ IsUnram (ξ * ((a i)⁻¹).comp (nm w))) fdeg hf hs
    (by
      rintro w' i i' y ⟨ξ, hξ, rfl, hu⟩ ⟨ξ', hξ', h', hu'⟩
      obtain rfl := (polFacts _).2.2.1 _ _ _ _ h'
      refine hind _ ((ha i).mul (ha i').inv) w' (un_div hu' hu ?_) w
      ext1 x
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
      rw [mul_comm (ξ x), mul_comm (ξ x), mul_comm ((a i) _)]
      group)
    (by
      intro i
      have h1 := congrArg natDegree (hm _ (ha i).inv)
      rw [Finset.prod_comm, natDegree_prod _ _ fun i' _ => Finset.prod_ne_zero_iff.2 fun j _ => lin_ne _,
        natDegree_prod _ _ fun w' _ h0 => by
          have := congrArg (eval 0) h0
          rw [eval_comp, eval_pow, eval_X, zero_pow (hf w').ne', ((polFacts _).2.2.2 _ _).1] at this
          simp at this] at h1
      rw [Finset.card_filter, Finset.sum_mul]
      refine Eq.trans (Finset.sum_congr rfl fun i' _ => ?_) (h1.trans (Finset.sum_congr rfl fun w' _ => ?_))
      · rw [natDegree_prod _ _ fun j _ => lin_ne _, Finset.sum_congr rfl fun j _ => lin_deg _, ← Finset.card_filter]
        split_ifs with hr
        · rw [one_mul, hc _ ((ha i').mul (ha i).inv) w hr]
        · rw [zero_mul, eq_comm, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          exact fun j hj hu => hr (hup' _ j hj hu w)
      · rw [natDegree_comp, natDegree_X_pow, ((polFacts _).2.2.2 _ _).2.1, mul_comm]
        rfl)
  intro y hy
  obtain ⟨i, ζ, hζ, rfl, hu⟩ := key w y hy
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
    ((((ζ * ((a i)⁻¹).comp (nm w)) (unif _) : ℂˣ) : ℂ)⁻¹) (hf w)
  have h0 : (∏ w, (pol (s w) (((a i)⁻¹).comp (nm w))).comp (X ^ fdeg w)).eval x = 0 := by
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
    rw [eval_comp, eval_pow, eval_X, hx]
    exact (((polFacts _).2.2.2 _ _).2.2.1 _).2 ⟨ζ, ⟨hζ, hy⟩, hu, mul_inv_cancel₀ (Units.ne_zero _)⟩
  rw [← hm _ (ha i).inv, eval_prod] at h0
  obtain ⟨j, hj, h0⟩ := Finset.prod_eq_zero_iff.1 h0
  rw [eval_prod] at h0
  obtain ⟨i', -, h0⟩ := Finset.prod_eq_zero_iff.1 h0
  obtain ⟨h1, h2⟩ := lin_root h0
  have h3 := ((normVal ℚ K v w _).1 h1).2
  have h4 : ((a i' * (a i)⁻¹).comp (nm w)) (unif _) = (ζ * ((a i)⁻¹).comp (nm w)) (unif _) := by
    rw [← hup _ j hj w, MonoidHom.comp_apply, h3]
    refine Units.ext ?_
    have h5 := congrArg (· ^ fdeg w) h2
    simp only [mul_pow, one_pow, hx] at h5
    rw [Units.val_pow_eq_pow_val]
    exact (mul_inv_eq_one₀ (Units.ne_zero _)).1 h5
  have h6 : ζ = (a i').comp (nm w) := by
    refine (polFacts _).2.1 _ _ (un_div hu (hup' _ j hj h1 w) ?_) ?_
    · ext1 x
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply]
      group
    · simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply] at h4 ⊢
      exact (mul_right_cancel h4).symm
  subst h6
  exact ⟨i', hζ, rfl⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adK :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdK := by
  intro K _ _ _ hK D hD P hP v w
  obtain ⟨η, hη⟩ := matchAd K hK D hD P hP
  obtain ⟨h1, h2, h3⟩ := hη v
  have hν : IsSmoothChar (D.ν v) :=
    GroundTheory.Global.isOpen_ker_of_continuous v GroundTheory.Global.Complex.units_noSmallSubgroups _ (D.unit v).1
  have sf := fun w : PlacesOver K v => suppFacts K 3 (by norm_num) P w.1
  choose s hs using fun w => (sf w).1
  have key := core ![D.ν v, 1, (D.ν v)⁻¹] (fun i => by fin_cases i; exacts [hν, isSmoothChar_one, hν.inv])
    (fun j => (η ^ j).loc v)
    (fun j hj w => by
      have := Finset.mem_range.1 hj
      interval_cases j
      · rw [pow_zero]; rfl
      · rw [pow_one]; exact h1 w)
    h2 s
    (fun w => by
      obtain ⟨-, h4, h5⟩ := (sf w).2.2.1 _ (hs w)
      have := Multiset.card_nsmul_le_sum (s := (s w).map Sigma.fst) (a := 1) fun x hx => by
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
        exact h5 y hy
      simpa [h4] using this)
    (fun θ hθ => by
      rw [← h3 s hs θ hθ]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Fin.prod_univ_three, Matrix.cons_val, one_mul, mul_assoc]) w
  have hch : ∀ t, SuppAt P w.1 t → ∀ ζ ∈ chars t,
      ζ = (D.ν v).comp (nm w) ∨ ζ = 1 ∨ ζ = ((D.ν v).comp (nm w))⁻¹ := by
    rintro t ht ζ ⟨hζ, hm⟩
    obtain rfl := (sf w).2.1 _ _ ht (hs w)
    obtain ⟨i, hi, e⟩ := key _ hm
    obtain rfl := (polFacts _).2.2.1 _ _ _ _ e
    fin_cases i
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
  refine ⟨⟨((sf w).2.2.1 _ (hs w)).1.2 fun y hy => ?_, fun t ht ζ hζ => ?_⟩, hch⟩
  · obtain ⟨i, hi, rfl⟩ := key y hy
    rfl
  · have hn : ‖((ζ (unif (w.1.adicCompletion K)) : ℂˣ) : ℂ)‖ = 1 := by
      rcases hch t ht ζ hζ with rfl | rfl | rfl
      · exact (D.unit v).2 _
      · simp
      · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, inv_eq_one]
        exact (D.unit v).2 _
    have hq : (1 : ℝ) < Ideal.absNorm w.1.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w.1
    rw [hn]
    exact ⟨Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num), Real.one_lt_rpow hq (by norm_num)⟩
end
end

section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GroundTheory.Global.SemiLocal
open Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd

open private Ad3P.SEGAux.frobenius_eigenvalues_trace_zero_adjoint Ad3P.SEGAux.charEig_cyc_inv Ad3P.SEGAux.algSat_eq from PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.FrobeniusEigenvaluesTraceZeroAdjoint

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem

private theorem unif_val {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (μ : kˣ →* ℂˣ) (hμ : GroundTheory.LocalField.IsUnramifiedChar μ) : μ (unif k) = μ (GroundTheory.LocalField.unifUnit k) := by
  obtain ⟨⟨h1, h2⟩, -⟩ := polFacts k
  have hord := GroundTheory.LocalField.ord_unifUnit (K := k)
  have hle : ∀ {x : k}, x ≠ 0 → (ValuativeRel.valuation k x ≤ 1 ↔ 0 ≤ GroundTheory.LocalField.ord x) := fun {x} hx => by
    have h0 := GroundTheory.LocalField.mem_valBall_iff_le_ord (n := 0) hx
    rwa [GroundTheory.LocalField.mem_valBall_zero_iff, Valuation.mem_integer_iff] at h0
  have hlt : ∀ {x : k}, x ≠ 0 → (ValuativeRel.valuation k x < 1 ↔ 1 ≤ GroundTheory.LocalField.ord x) := fun {x} hx => by
    have h0 := GroundTheory.LocalField.mem_valBall_iff_le_ord (n := 1) hx
    rwa [GroundTheory.LocalField.mem_valBall_one_iff] at h0
  have a1 := (hlt (unif k).ne_zero).1 h1
  have a2 := h2 _ ((hlt (GroundTheory.LocalField.unifUnit k).ne_zero).2 hord.ge)
  have a3 : ValuativeRel.valuation k ((GroundTheory.LocalField.unifUnit k * (unif k)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ a2 zero_le'
  have a4 := (hle (Units.ne_zero _)).1 a3
  rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_units_inv, hord] at a4
  have a5 : GroundTheory.LocalField.ord ((unif k : kˣ) : k) = 1 := by omega
  have a6 := GroundTheory.LocalField.isUnramifiedChar_iff.1 hμ (unif k * (GroundTheory.LocalField.unifUnit k)⁻¹) (by
    rw [GroundTheory.LocalField.ord_units_mul, GroundTheory.LocalField.ord_units_inv, hord, a5]; simp)
  rwa [map_mul, map_inv, mul_inv_eq_one] at a6

private theorem charpoly_inv {M M' : Matrix (Fin 2) (Fin 2) ℂ} (h : M * M' = 1) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : M.charpoly = X ^ 2 - C (a + b) * X + C (a * b)) : M'.charpoly = (X - C b⁻¹) * (X - C a⁻¹) := by
  rw [Matrix.charpoly_fin_two] at hc
  have e0 := congrArg (eval 0) hc
  have e1 := congrArg (eval 1) hc
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : M.det = a * b := by simpa using e0
  have ht : M.trace = a + b := by
    rw [hd] at e1
    linear_combination -e1
  have hi : M' = (a * b)⁻¹ • M.adjugate := by
    rw [← Matrix.inv_eq_right_inv h, Matrix.inv_def, hd, Ring.inverse_eq_inv']
  have t' : M'.trace = b⁻¹ + a⁻¹ := by
    rw [hi, Matrix.trace_smul, Matrix.adjugate_fin_two, Matrix.trace_fin_two]
    rw [Matrix.trace_fin_two] at ht
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul]
    field_simp
    linear_combination ht
  have d' : M'.det = b⁻¹ * a⁻¹ := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_one, hd] at this
    field_simp
    linear_combination this
  rw [Matrix.charpoly_fin_two, t', d']
  simp only [map_add, map_mul]
  ring

private theorem frobEig_unique {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂ}
    (h : FrobEig ι r w B) (h' : FrobEig ι r w B') : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := ((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ)
  have e2 := congrArg Polynomial.roots e
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e2

private theorem ev_under (K : Type) [Field K] [NumberField K] {Q : HeightOneSpectrum (𝓞 K) → Prop}
    (h : ∀ᶠ w in Filter.cofinite, Q w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ∀ w : PlacesOver K v, Q w.1 := by
  refine Filter.eventually_cofinite.2 (((Filter.eventually_cofinite.1 h).image fun w => w.under (𝓞 ℚ)).subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, HeightOneSpectrum.ext w.2.over.symm⟩

private theorem frobEig_geom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (v : HeightOneSpectrum (𝓞 ℚ)) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ A : ValuationSubring Ω, IsPlaceOver A v → (∀ s ∈ Ine (F := ℚ) A, ρ s = 1) ∧ ∀ σ : G ℚ Ω, IsFrob A (normV v) σ →
      (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.map ι.toRingHom = X ^ 2 - C (a + b) * X + C (a * b)) :
    FrobEig ι ρ v {b⁻¹, a⁻¹} := fun A hA => by
  obtain ⟨h1, h2⟩ := h A hA
  refine ⟨h1, fun σ hσ => ?_⟩
  have e := h2 σ hσ
  rw [← Matrix.charpoly_map] at e ⊢
  have hm : (ρ σ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom * (ρ σ⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).map ι.toRingHom = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [charpoly_inv hm ha hb e]
  simp

private theorem algSat_inj (n q : ℕ) (hq : q ≠ 0) {B B' : Multiset ℂˣ} (h : algSat n q B = algSat n q B') : B = B' := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hq)) _).ne'
  rw [Ad3P.SEGAux.algSat_eq, Ad3P.SEGAux.algSat_eq] at h
  exact Multiset.map_injective (fun x y e => Units.ext (mul_left_cancel₀ hc e)) h

private theorem algSat_three (q : ℕ) (t : ℂˣ) : algSat 3 q {t, 1, t⁻¹} = {(q : ℂ) * t, (q : ℂ), (q : ℂ) * (t⁻¹ : ℂˣ)} := by
  have h : ((((q : ℝ) ^ (((3 : ℝ) - 1) / 2) : ℝ)) : ℂ) = q := by
    have : (((3 : ℝ) - 1) / 2) = 1 := by norm_num
    rw [this, Real.rpow_one]
    simp
  simp [algSat, h]

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem

open UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdjointSystem in
theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.adSysOf :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.AdSysOf := by
  intro l _ Ω _ _ _ ι N _ χ D g ρ hR hS K _ _ _ _ P hA
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  have h0 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
    (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)
  have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, v ∉ D.bad :=
    Filter.eventually_cofinite.2 (by simpa using D.bad.finite_toSet)
  filter_upwards [hR, hl, hb, ev_under K hA.2] with v h1 h2 h3 h4 w
  obtain ⟨B, hB, hF⟩ := h4 w
  obtain ⟨α, β, e1, e2, e3⟩ := hS.2 v h3
  have hp : Ad3.pOf v = normV v := by
    simp [Ad3.pOf, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq' : Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal ^ fdeg w := (normVal ℚ K v w (1 : _ →* ℂˣ)).2.2.2
  have hnq : normV w.1 = normV v ^ fdeg w := by
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hq'
  have hu : w.1.under (𝓞 ℚ) = v := HeightOneSpectrum.ext w.2.over.symm
  have e4 : D.ν v (unif (v.adicCompletion ℚ)) = α / β := (unif_val (D.ν v) (D.unr v h3)).trans e3
  have g1 : FrobEig ι ρ v {(β : ℂ)⁻¹, (α : ℂ)⁻¹} := by
    refine frobEig_geom ι ρ v α β α.ne_zero β.ne_zero fun A hA' => ?_
    refine ⟨(h1 A hA').1, fun σ hσ => ?_⟩
    rw [(h1 A hA').2 σ hσ, e1, e2, hp]
  have g2 := Ad3P.SEGAux.frobenius_eigenvalues_trace_zero_adjoint ι ρ v _ _ (inv_ne_zero β.ne_zero) (inv_ne_zero α.ne_zero) g1
  have g3 := UpperTheory.frobenius_eigenvalues_twist ℚ Ω l ι 3 _ _ v _ _ g2 (Ad3P.SEGAux.charEig_cyc_inv ι v h2)
  have g4 := (UpperTheory.frobenius_power_compatibility ℚ K Ω l ι w.1 (fdeg w) (by rw [hu]; exact hnq)).1 3 _ _ (by rw [hu]; exact g3)
  have g5 := frobEig_unique hF g4
  have hnz : normV w.1 ≠ 0 := by
    have := Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  rw [e4]
  have hfin : B = {(α / β) ^ fdeg w, 1, ((α / β) ^ fdeg w)⁻¹} := by
    refine algSat_inj 3 (normV w.1) hnz (g5.trans ?_)
    rw [algSat_three, hnq]
    have hα := α.ne_zero
    have hβ := β.ne_zero
    have x1 : (((β : ℂ)⁻¹ / (α : ℂ)⁻¹) * (normV v : ℂ)) ^ fdeg w =
        ((normV v ^ fdeg w : ℕ) : ℂ) * (((α / β) ^ fdeg w : ℂˣ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_comm]
      congr 2
      field_simp
    have x3 : (((α : ℂ)⁻¹ / (β : ℂ)⁻¹) * (normV v : ℂ)) ^ fdeg w =
        ((normV v ^ fdeg w : ℕ) : ℂ) * ((((α / β) ^ fdeg w)⁻¹ : ℂˣ) : ℂ) := by
      push_cast
      rw [mul_pow, mul_comm, ← inv_pow]
      congr 2
      field_simp
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
    rw [x1, x3]
    simp
  rw [← hfin]
  exact hB
end

section
namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter


end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end

section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.EG GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.DirichletHecke
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
end

section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
