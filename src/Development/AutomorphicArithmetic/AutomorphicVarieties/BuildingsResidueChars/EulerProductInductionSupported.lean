import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsPolynomialPairFunctionalEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.RegroupBC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.PairGOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.EulerdShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.CrossGOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SecDiff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.NormLoc

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem sign_ex (c : HeckeCharacter ℚ) :
    ∃ δ : Bool, ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) = if δ then -1 else 1 := by
  have hsq : ∀ w : InfinitePlace ℚ, (c.infiniteComponent w (-1) : ℂ) * (c.infiniteComponent w (-1) : ℂ) = 1 := by
    intro w
    rw [← Circle.coe_mul, ← map_mul, neg_mul_neg, one_mul, map_one, Circle.coe_one]
  rcases mul_self_eq_one_iff.1 (hsq default) with h | h
  · exact ⟨false, fun w => by rw [Subsingleton.elim w default, h]; rfl⟩
  · exact ⟨true, fun w => by rw [Subsingleton.elim w default, h]; rfl⟩

private theorem unr_of {η : HeckeCharacter ℚ} {v : Ad3.Pl} (h : (toH η).UnrAt v) :
    IsUnramifiedChar (localChar η v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  rw [← Ad3P.DihedralUnramifiedPlaces.loc_eq]
  apply h x
  show Valued.v (x : Ad3.Qv v) = 1
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v x.ne_zero, neg_eq_zero] at hx
  have h0 : Valued.v (x : Ad3.Qv v) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [← WithZero.exp_log h0, hx, WithZero.exp_zero]

private theorem unr_mul {c η : HeckeCharacter ℚ} {v : Ad3.Pl} (h₁ : IsUnramifiedChar (localChar c v))
    (h₂ : IsUnramifiedChar (localChar η v)) : IsUnramifiedChar (localChar (c * η) v) := by
  refine isUnramifiedChar_iff.2 fun x hx => ?_
  have e : localChar (c * η) v x = localChar c v x * localChar η v x := Units.ext rfl
  rw [e, isUnramifiedChar_iff.1 h₁ x hx, isUnramifiedChar_iff.1 h₂ x hx, one_mul]

private theorem val_mul' (c η : HeckeCharacter ℚ) (v : Ad3.Pl) :
    (toH (c * η)).val v = (toH c).val v * (toH η).val v := Units.ext rfl

private theorem norm_val (c : HeckeCharacter ℚ) (v : Ad3.Pl) : ‖((toH c).val v : ℂ)‖ = 1 :=
  Circle.norm_coe _

private theorem tri_mul (a x y : ℂˣ) : tri a (x * y) = (tri a x).map (· * (y : ℂ)) := by
  simp [tri, mul_assoc]

private theorem tri_norm {a x : ℂˣ} (ha : ‖(a : ℂ)‖ = 1) (hx : ‖(x : ℂ)‖ = 1) : ∀ b ∈ tri a x, ‖b‖ = 1 := by
  intro b hb
  simp only [tri, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.mem_cons,
    Multiset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl <;> simp [ha, hx]

theorem UpperTheory.euler_product_induction_unramified :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ D : Ad3.Dat, Ad3.An D →
        ∀ (η c : HeckeCharacter ℚ), EtaOK K η → IsOfFinOrder c → ∀ (S : Finset Ad3.Pl) (v : Ad3.Pl), D.bad ⊆ S → v ∈ S →
        (∀ u ∉ S, IsUnramifiedChar (localChar c u)) →
        (∀ u ∉ S, (toH η).UnrAt u ∧ ∀ w : PlacesOver K u, IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧
          Fintype.card (PlacesOver K u) * fdeg w = 2) →
        (∀ u ∈ S, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u)) →
        ∀ (MainNotions : Set (HeightOneSpectrum (𝓞 K))) (BL : HeightOneSpectrum (𝓞 K) → Multiset ℂ),
        (∀ w, w ∈ MainNotions ↔ w.under (𝓞 ℚ) ∈ (S : Set Ad3.Pl)) →
        (∀ p ∉ S, ∀ w : PlacesOver K p, BL w.1 = (par D (toH c) p).map (· ^ fdeg w)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG (eulerL K BL MainNotions) (eulerLd K BL MainNotions) β (Ideal.absNorm v.asIdeal : ℝ)
          (lin3 (D.ν v) (localChar c v) * lin3 (D.ν v) (localChar (c * η) v)) := by
  intro K _ _ _ _ D hD η c hη hc S v hbad hv hcu hηu hram MainNotions BL hSK hBL
  obtain ⟨δ, hδ⟩ := sign_ex c
  have A₁ : Ad3.admitted D c δ S := ⟨hc, hδ, hbad, hcu⟩
  have A₂ : Ad3.admitted D (c * η) (!δ) S := by
    refine ⟨hc.mul hη.fin, fun w => ?_, hbad, fun u hu => unr_mul (hcu u hu) (unr_of (hηu u hu).1)⟩
    have e : ((c * η).infiniteComponent w (-1) : ℂ) =
        (c.infiniteComponent w (-1) : ℂ) * (η.infiniteComponent w (-1) : ℂ) := rfl
    rw [e, hδ w, hη.sgn w]
    cases δ <;> simp
  obtain ⟨β, hβ, hP⟩ := UpperTheory.exists_polynomial_pair_functional_eq D hD c (c * η) δ S v A₁ A₂ hv hram
  obtain ⟨a, ha⟩ := UpperTheory.V.Z.Gam.regroupBC ℚ K 2 (S : Set Ad3.Pl) MainNotions (par D (toH c)) BL
    (fun p => ((toH η).val p : ℂ)) 0 3 Nat.prime_two hSK (by
      intro p hp
      have hp' : p ∉ S := fun h => hp (Finset.mem_coe.2 h)
      refine ⟨by simp [par, tri], fun b hb => ?_, fun w => ⟨?_, ((hηu p hp').2 w).2, hBL p hp' w⟩⟩
      · have hb1 : ‖b‖ = 1 := tri_norm ((D.unit p).2 _) (norm_val c p) b hb
        rw [norm_inv, hb1, Real.rpow_zero, inv_one]
        exact ⟨le_rfl, le_rfl⟩
      · exact IsPrimitiveRoot.coe_units_iff.2 ((hηu p hp').2 w).1)
  have e0 : (fun p => (par D (toH c) p).map (· * ((toH η).val p : ℂ) ^ 0)) = par D (toH c) := by
    funext p
    simp
  have e1 : (fun p => (par D (toH c) p).map (· * ((toH η).val p : ℂ) ^ 1)) = par D (toH (c * η)) := by
    funext p
    simp only [pow_one]
    unfold par
    rw [val_mul', tri_mul]
  refine ⟨β, hβ, UpperTheory.V.Z.Gam.pairGOps.2.2.1 _ _ _ _ β _ _ a hP (fun s hs => ?_) (fun s hs => ?_)⟩
  · rw [← (ha s).1 hs, Finset.prod_range_succ, Finset.prod_range_one, e0, e1,
      (UpperTheory.euler_product_adjoint_eq_standard D c δ S A₁ s).1, (UpperTheory.euler_product_adjoint_eq_standard D (c * η) _ S A₂ s).1]
  · rw [← (ha s).2 hs, Finset.prod_range_succ, Finset.prod_range_one, e0, e1,
      (UpperTheory.euler_product_adjoint_eq_standard D c δ S A₁ s).2, (UpperTheory.euler_product_adjoint_eq_standard D (c * η) _ S A₂ s).2]
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem cnt_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) (h : ∀ ζ ∈ chars s, ¬ IsUnram (ζ * χ)) : cnt s χ = 0 := by
  unfold cnt
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  rintro y hy ⟨ζ, hζ, rfl, hu⟩
  exact h ζ ⟨hζ, hy⟩ hu

private theorem pol_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : Multiset (IrrGL k)) (χ : kˣ →* ℂˣ) (h : cnt s χ = 0) : pol s χ = 1 := by
  obtain ⟨h0, hd, -⟩ := (polFacts k).2.2.2 s χ
  have e := eq_C_of_natDegree_eq_zero (hd.trans h)
  rw [e, eval_C] at h0
  rw [e, h0, C_1]

private theorem prod_sub {α M : Type} [CommMonoid M] (p : α → Prop) [Fintype {a // p a}] (S : Finset α) (g : α → M)
    (h1 : ∀ w : {a // p a}, w.1 ∈ S) (h2 : ∀ a ∈ S, ¬ p a → g a = 1) : ∏ a ∈ S, g a = ∏ w : {a // p a}, g w.1 := by
  rw [← Finset.prod_subtype (S.filter p) (p := p) (fun a => ⟨fun h => (Finset.mem_filter.1 h).2,
    fun h => Finset.mem_filter.2 ⟨h1 ⟨a, h⟩, h⟩⟩) g]
  refine (Finset.prod_subset (Finset.filter_subset _ _) fun a ha hn => h2 a ha fun hp => hn ?_).symm
  exact Finset.mem_filter.2 ⟨ha, hp⟩

theorem UpperTheory.satake_parameters_twisted_automorphic :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (P : CuspSub K 3) (ξ : HChar K)
        (MainNotions : Finset (HeightOneSpectrum (𝓞 K))) (B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ) (v : Ad3.Pl)
        (s : ∀ w : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (w.adicCompletion K))),
        GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ MainNotions →
        (∀ w ∉ MainNotions, (CG.mk (P.twist ξ)).HasSat w (B w)) → (∀ w, SuppAt P w (s w)) → (∀ w : PlacesOver K v, w.1 ∈ MainNotions) →
        (∀ w ∈ MainNotions, w.under (𝓞 ℚ) ≠ v → ∀ ζ ∈ chars (s w), ¬ IsUnram (ζ * ξ.loc w)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG (eulerL K (cx B) MainNotions) (eulerLd K (cx B) MainNotions) β (Ideal.absNorm v.asIdeal : ℝ)
          (∏ w : PlacesOver K v, (pol (s w.1) (ξ.loc w.1)).comp (X ^ fdeg w)) := by
  intro K _ _ _ P ξ MainNotions B v s hS hB hs hv hr
  have hex : ∀ w, ∃ s', SuppAt (P.twist ξ) w s' ∧ pol s' 1 = pol (s w) (ξ.loc w) ∧ cnt s' 1 = cnt (s w) (ξ.loc w) := fun w => by
    obtain ⟨s', h1, h2, -⟩ := suppTw K 3 (by omega) P w ξ (s w) (hs w)
    have hF := (polFacts (w.adicCompletion K)).2.2.2
    have e : pol s' 1 = pol (s w) (ξ.loc w) := by rw [h2, mul_one]
    exact ⟨s', h1, e, by rw [← (hF s' 1).2.1, e, (hF _ _).2.1]⟩
  choose s' h1 h2 h3 using hex
  have hz : ∀ w ∈ MainNotions, ¬ w.asIdeal.LiesOver v.asIdeal → cnt (s w) (ξ.loc w) = 0 := fun w hw hn =>
    cnt_zero _ _ (hr w hw fun e => hn (by subst e; exact ⟨rfl⟩))
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨β, hβ, hP⟩ := sideX K 3 (by omega) (P.twist ξ) MainNotions hS B hB s' (Ideal.absNorm v.asIdeal)
    (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq (fun w hw => ⟨h1 w, fun hc => by
      have hl : w.asIdeal.LiesOver v.asIdeal := by
        by_contra hn
        exact hc ((h3 w).trans (hz w hw hn))
      exact (normVal ℚ K v ⟨w, hl⟩ 1).2.2.2⟩)
  refine ⟨β, hβ, ?_⟩
  have e : (∏ w ∈ MainNotions, (pol (s' w) 1).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal)) =
      ∏ w : PlacesOver K v, (pol (s w.1) (ξ.loc w.1)).comp (X ^ fdeg w) := by
    simp only [h2]
    exact prod_sub (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal.LiesOver v.asIdeal) MainNotions
      (fun w => (pol (s w) (ξ.loc w)).comp (X ^ v.asIdeal.inertiaDeg' w.asIdeal)) hv
      (fun w hw hn => by rw [pol_one _ _ (hz w hw hn), one_comp])
  rw [← e]
  exact hP
end

section
open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem ram3 {ν c : kˣ →* ℂˣ} (hν : IsUnram ν) (hc : ¬ IsUnram c) : Ram3 ν c :=
  ⟨fun h => hc (unr_cancel hν h), hc, fun h => hc (unr_cancel (unr_inv hν) h)⟩

private theorem lin_zero (a : kˣ →* ℂˣ) : (lin a).eval 0 = 1 := by
  unfold lin
  split_ifs <;> simp

private theorem local_linear_factor_eval_zero (a b : kˣ →* ℂˣ) : (lin3 a b).eval 0 = 1 := by
  simp only [lin3, eval_mul, lin_zero, mul_one]

end Loc

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem unr_iff (u : Ad3.Pl) (a : (u.adicCompletion ℚ)ˣ →* ℂˣ) : IsUnramifiedChar a ↔ IsUnram a := by
  haveI : (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [isUnramifiedChar_iff]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq u x.ne_zero, neg_eq_zero,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion ℚ)) Valued.v).eq_one_iff_eq_one]
  have h0 : Valued.v (x : u.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

private theorem localChar_mul' (c η : HeckeCharacter ℚ) (u : Ad3.Pl) :
    localChar (c * η) u = localChar c u * localChar η u := by
  ext x
  rfl

private theorem under_eq {K : Type} [Field K] [NumberField K] {p : Ad3.Pl} (w : PlacesOver K p) : w.1.under (𝓞 ℚ) = p :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem exists_above (K : Type) [Field K] [NumberField K] (S : Finset Ad3.Pl) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ w.under (𝓞 ℚ) ∈ S := by
  refine ⟨S.biUnion fun p => (Finset.univ : Finset (PlacesOver K p)).map (Function.Embedding.subtype _), fun w => ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, w', rfl⟩
    change w'.1.under (𝓞 ℚ) ∈ S
    rwa [under_eq]
  · exact fun h => ⟨_, h, ⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem unr_of_norm {K : Type} [Field K] [NumberField K] {η : HeckeCharacter ℚ} (hη : EtaOK K η) (c : HChar ℚ)
    {u : Ad3.Pl} (hu : (toH η).UnrAt u) (w : PlacesOver K u) (h : IsUnram ((c.loc u).comp (nm w))) : IsUnram (c.loc u) := by
  have hc := (((hη.loc u w).2.2 _ (GlobalTheory.HeckeComp.smooth_loc c u)).2.2 h)
  have hpos : 0 < ∑ w' : PlacesOver K u, fdeg w' :=
    lt_of_lt_of_le (normVal ℚ K u w 1).2.2.1 (Finset.single_le_sum (f := fun w' : PlacesOver K u => fdeg w')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
  rw [← hc] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  have hj' := (Finset.mem_filter.1 hj).2
  have hp : ∀ j : ℕ, IsUnram ((toH η ^ j).loc u) := fun j => by
    induction j with
    | zero => intro x hx; rfl
    | succ j ih =>
      intro x hx
      rw [pow_succ]
      change (toH η ^ j).loc u x * (toH η).loc u x = 1
      rw [ih x hx, (unrAt_iff _ _).1 hu x hx, one_mul]
  exact unr_cancel (hp j) (mul_comm (c.loc u) _ ▸ hj')

private theorem tri_pow (a x : ℂˣ) (f : ℕ) :
    ((({a ^ f, 1, (a ^ f)⁻¹} : Multiset ℂˣ).map (· * x ^ f)).map fun b : ℂˣ => (b : ℂ)) = (tri a x).map (· ^ f) := by
  simp [tri, mul_pow]

theorem UpperTheory.euler_product_induction_supported :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ D : Ad3.Dat, Ad3.An D →
        ∀ (P : CuspSub K 3) (η c : HeckeCharacter ℚ), EtaOK K η → IsOfFinOrder c → ∀ (S₀ : Finset Ad3.Pl) (v : Ad3.Pl)
        (s : ∀ w : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (w.adicCompletion K))), (∀ w, SuppAt P w (s w)) →
        D.bad ⊆ S₀ → v ∈ S₀ →
        (∀ u ∉ S₀, (toH η).UnrAt u ∧ ∀ w : PlacesOver K u, IsPrimitiveRoot ((toH η).val u) (fdeg w) ∧
          Fintype.card (PlacesOver K u) * fdeg w = 2 ∧ w.1 ∉ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∧
          (CG.mk P).HasSat w.1 {D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w, 1, (D.ν u (unif (u.adicCompletion ℚ)) ^ fdeg w)⁻¹}) →
        (∀ u ∈ S₀, u ≠ v → Ram3 (D.ν u) (localChar c u) ∧ Ram3 (D.ν u) (localChar (c * η) u) ∧
          ∀ w : PlacesOver K u, ∀ ζ ∈ chars (s w.1), ¬ IsUnram (ζ * (localChar c u).comp (nm w))) →
        lin3 (D.ν v) (localChar c v) * lin3 (D.ν v) (localChar (c * η) v) =
          ∏ w : PlacesOver K v, (pol (s w.1) ((localChar c v).comp (nm w))).comp (X ^ fdeg w) := by
  intro K _ _ _ hK D hD P η c hη hc S₀ v s hs hbad hv hout hin
  obtain ⟨ξ, hξ⟩ := normLoc ℚ K (toH c)
  obtain ⟨S, hS⟩ : ∃ S : Finset Ad3.Pl, ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ (toH c).UnrAt u :=
    ⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified (toH c)).toFinset, fun u => by simp⟩
  obtain ⟨MainNotions, hSK⟩ := exists_above K S
  have out0 : ∀ u ∉ S, u ∉ S₀ := fun u hu h => hu ((hS u).2 (Or.inl h))
  have outc : ∀ u ∉ S, (toH c).UnrAt u := fun u hu => not_not.1 fun h => hu ((hS u).2 (Or.inr h))
  have hex : ∀ w : HeightOneSpectrum (𝓞 K), ∃ B : Multiset ℂˣ, (w ∉ MainNotions → (CG.mk (P.twist ξ)).HasSat w B) ∧
      ∀ p ∉ S, ∀ w' : PlacesOver K p, w'.1 = w → (B.map fun b : ℂˣ => (b : ℂ)) = (par D (toH c) p).map (· ^ fdeg w') := by
    intro w
    by_cases hw : w.under (𝓞 ℚ) ∈ S
    · refine ⟨0, fun h => absurd ((hSK w).2 hw) h, fun p hp w' e => ?_⟩
      subst e
      rw [under_eq] at hw
      exact absurd hw hp
    · obtain ⟨u1, v1⟩ := (hξ _ ⟨w, ⟨rfl⟩⟩).2.1 (outc _ hw)
      have h := (((hout _ (out0 _ hw)).2 ⟨w, ⟨rfl⟩⟩).2.2.2).twist u1
      rw [CG.twist_mk, v1] at h
      refine ⟨_, fun _ => h, fun p hp w' e => ?_⟩
      obtain ⟨w', hw'⟩ := w'
      obtain rfl : w' = w := e
      obtain rfl : p = w'.under (𝓞 ℚ) := HeightOneSpectrum.ext hw'.over
      exact tri_pow _ _ _
  choose B hB1 hB2 using hex
  obtain ⟨β, hβ, pL⟩ := UpperTheory.euler_product_induction_unramified K hK D hD η c hη hc S v (fun u hu => (hS u).2 (Or.inl (hbad hu)))
    ((hS v).2 (Or.inl hv)) (fun u hu => (unr_iff u _).2 ((unrAt_iff _ u).1 (outc u hu)))
    (fun u hu => ⟨(hout u (out0 u hu)).1, fun w => ⟨((hout u (out0 u hu)).2 w).1, ((hout u (out0 u hu)).2 w).2.1⟩⟩)
    (fun u hu hne => by
      by_cases h0 : u ∈ S₀
      · exact ⟨(hin u h0 hne).1, (hin u h0 hne).2.1⟩
      · have hν : IsUnram (D.ν u) := (unr_iff u _).1 (D.unr u fun h => h0 (hbad h))
        have hr : ¬ IsUnram (localChar c u) := fun h => ((hS u).1 hu).resolve_left h0 ((unrAt_iff _ u).2 h)
        refine ⟨ram3 hν hr, ram3 hν fun h => hr ?_⟩
        rw [localChar_mul', mul_comm] at h
        exact unr_cancel ((unrAt_iff _ u).1 (hout u h0).1) h)
    (MainNotions : Set _) (cx B) (fun w => by simpa using hSK w) (fun p hp w => hB2 w.1 p hp w rfl)
  obtain ⟨β', hβ', pR⟩ := UpperTheory.satake_parameters_twisted_automorphic K P ξ MainNotions B v s
    (fun w hw => (hSK w).2 (not_not.1 fun h => ((hout _ (out0 _ h)).2 ⟨w, ⟨rfl⟩⟩).2.2.1 hw)) hB1 hs
    (fun w => (hSK w.1).2 (by rw [under_eq]; exact (hS v).2 (Or.inl hv)))
    (fun w hw hne ζ hζ => by
      rw [(hξ (w.under (𝓞 ℚ)) ⟨w, ⟨rfl⟩⟩).1]
      by_cases h0 : w.under (𝓞 ℚ) ∈ S₀
      · exact (hin _ h0 hne).2.2 ⟨w, ⟨rfl⟩⟩ ζ hζ
      · intro h
        obtain ⟨hζ', hm⟩ := hζ
        obtain ⟨μ, hμ, e⟩ := (suppFacts K 3 (by omega) P w).2.2.2.1 _ _ (hs w) ((hout _ h0).2 ⟨w, ⟨rfl⟩⟩).2.2.2 _ hm
        rw [(polFacts _).2.2.1 _ _ _ _ e] at h
        exact ((hS _).1 ((hSK w).1 hw)).resolve_left h0
          ((unrAt_iff _ _).2 (unr_of_norm hη (toH c) (hout _ h0).1 ⟨w, ⟨rfl⟩⟩ (unr_cancel hμ h))))
  have e : ∀ w : PlacesOver K v, ξ.loc w.1 = (localChar c v).comp (nm w) := fun w => (hξ v w).1
  simp only [e] at pR
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  refine crossGOf expAlg expIndep secDiff _ _ _ _ _ _ _ (by exact_mod_cast hq) hβ hβ' ?_ ?_ pL pR
  · rw [eval_mul, local_linear_factor_eval_zero, local_linear_factor_eval_zero, mul_one]
  · rw [eval_prod]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [eval_comp, eval_pow, eval_X, zero_pow (normVal ℚ K v w 1).2.2.1.ne']
    exact ((polFacts _).2.2.2 _ _).1
end
