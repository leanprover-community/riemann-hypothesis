import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WsLink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicPointGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.LinkTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PfConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPairAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.AcClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.FormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.HasFlagPush
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.RedPsi
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.RedDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.IneTriv
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondA
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondC
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CondDRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TraceOfCp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.MapsPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.ContinuousLinearClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.H4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWinPm
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.CharpolySmulScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PsiCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.IrrOfStab
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.PairJAdj
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.SupComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAut4
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutQN
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Across
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PmSeedP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.CuspidalRankFourRegularAlgebraicTotallyComplex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TwistInvarianceAutomorphic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.CycIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArith
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.H5
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.TanOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNiceFour
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.RRFree

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk
open private exists_conj ne_top val_nat fin_nat eq_of_mem from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfMem
open private bu bu_val bu_open eq_of_ker dec_of from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.EqOfKer
open private pre_ex from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.LinkEx
theorem UpperTheory.Gal.projectedFormsSystemPart.exists_two_links_same_kappa_not_dvd_of_fit_deep :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∃ c₁ : Coef l, ∀ (c' : Coef l) (h : c.O ≤ c'.O), c₁.O ≤ c'.O → ∃ K K' : Link T c' h, K'.κ = K.κ ∧ ¬ K'.s.p ∣ K.s.p := by
  intro hU Ω _ _ _ l _ c D T hF hD
  have hC : Ctx2 D ∨ Ctx3 D := hF.2.imp And.left And.left
  have hG : D.Good := hC.elim And.left And.left
  have hO := hF.1
  obtain ⟨P⟩ := pre_ex T hO hG hC
  obtain ⟨k1, k2, k3⟩ := kapCont P
  obtain ⟨u1, u2, u3⟩ := kapUnr P hG
  let Q : QCh T :=
    { κ := P.κ, β := P.βL, t := P.tL, κ_cont := k1, β_cont := k2, t_cont := k3, β_t := fun _ hg => P.β_t hg,
      β_red := fun _ => P.β_red _, conj := kapConj P hD, t_unr := u1, unr := u2, tame := u3, mu := kapMu P hG,
      cyc := kapCyc P hG }
  obtain ⟨c₁, -, hL, hκ, hβ, -⟩ := Pr.coefEx l c T.L Ω Q.κ Q.β Q.κ_cont Q.β_cont
  refine ⟨c₁, fun c' h h₁ => ?_⟩
  obtain ⟨κ, a1, a2, -⟩ := liftO c' Q.κ Q.κ_cont fun g => h₁ (hκ g)
  obtain ⟨β, b1, b2, b3⟩ := liftO c' Q.β Q.β_cont fun g => h₁ (hβ g)
  obtain ⟨X⟩ := ochOf Q c' h κ β a1 b1 a2 b2 fun g => b3 g (Q.β_red g)
  have key : ∀ Y : SetD T, ∃ K : Link T c' h, K.κ = X.κ ∧ K.s = Y.s := fun Y => by
    obtain ⟨V, hV⟩ := hU.lev l T.L Ω Y.s Y.s.S Y.fin subset_rfl Y.s.split
    obtain ⟨r, r1, r2, r3⟩ := residEx X Y V hG hO hV
    obtain ⟨σ, hσ, hc⟩ := Y.cc
    obtain ⟨g₀, -, hg₀⟩ := Y.om0
    exact ⟨{ s := Y.s, V := V, hV := hV, noMu := noMu hG T.L g₀ hg₀, large := fun τ x => h₁ (hL τ x), e := Y.e, hA := Y.hA,
             κ := X.κ, β := X.β, t := X.t, κ_cont := X.κ_cont, β_cont := X.β_cont, t_cont := X.t_cont, β_t := X.β_t,
             β_red := X.β_red, conj := fun g g' e => X.conj σ hσ g g' (hc g g' e), t_unr := X.t_unr,
             unr := fun A v hA hv g hg =>
               ⟨X.unr A (Y.away A v hA hv) hg, (((barFacts hG).2.2 A (Y.away A v hA hv) _ ⟨hg.1, hg.2⟩)).2⟩
             tame := X.tame
             mu := fun v g hg => by
               obtain ⟨a, ha⟩ := (prFacts l T.L Ω Y.s V).2.2.2 v g hg
               exact X.mu g a ha
             cyc := X.cyc, r := r, chib := fun i g => by rw [r1]; rfl
             psib := r2, th := r3, v0 := v0ok X Y V hG r r1 }, rfl, rfl⟩
  obtain ⟨Y, -⟩ := UpperTheory.Gal.projectedFormsSystemPart.setAv T hG hO 1 one_ne_zero
  obtain ⟨Y', hY⟩ := UpperTheory.Gal.projectedFormsSystemPart.setAv T hG hO Y.s.p Y.s.p_prime.ne_zero
  obtain ⟨K, k1, k2⟩ := key Y
  obtain ⟨K', k3, k4⟩ := key Y'
  exact ⟨K, K', k3.trans k1.symm, by rw [k2, k4]; exact hY⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
section Abstract
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
private theorem pf_const [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) {y : R} (hy : IsIntegral O y) :
    ∃ a, y = algebraMap O R a := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
  refine ⟨a, ?_⟩
  by_contra hne
  letI : Algebra (ResidueField O) R := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R) h0).toAlgebra
  haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (ResidueField O) (y - algebraMap O R a) := (hy.sub isIntegral_algebraMap).tower_top
  exact ha (h1.isUnit (sub_ne_zero.2 hne))
private theorem pf_sect (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ s : B →ₐ[O] R, (∀ b ∈ maximalIdeal B, s b = 0) ∧ ∀ (f : B →ₐ[O] R) (b : B), (∃ a, f b = algebraMap O R a) → f b = s b := by
  let j : ResidueField O →ₐ[O] R := Ideal.Quotient.liftₐ (maximalIdeal O) (Algebra.ofId O R) h0
  refine ⟨j.comp (res O B), fun b hb => ?_, ?_⟩
  · rw [AlgHom.comp_apply, (res_eq_zero_iff O B b).2 hb, map_zero]
  · rintro f b ⟨a, ha⟩
    rw [AlgHom.comp_apply, ← res_map f, ha, AlgHom.commutes, AlgHom.commutes]
private theorem pf_cont {Γ B : Type} [TopologicalSpace Γ] [CommRing B] [Algebra O B] [IsCO O B] (f : B →ₐ[O] R) {u : Γ → B}
    (hu : AdicCont (maximalIdeal B) u) : AdicCont (maximalIdeal R) fun g => f (u g) := fun N => by
  have hle : maximalIdeal B ^ N ≤ (maximalIdeal R ^ N).comap (f : B →+* R) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hu N).comp (Ideal.quotientMap _ (f : B →+* R) hle)
private theorem pf_lam {l : ℕ} [Fact l.Prime] {F : W.GFrame l} [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ : W.LamObj r)
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : Λ.Λ →ₐ[O] R)
    (hf : ∀ v i g, ∃ a, f (Λ.κ v i g) = algebraMap O R a) (x : Λ.Λ) : ∃ a, f x = algebraMap O R a := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 Λ.Λ
  have hi : W.IsInert r fun v i => W.pushCh (f : Λ.Λ →+* R) (Λ.κ v i) := fun v i => by
    obtain ⟨ψ, hψ, he⟩ := Λ.inert v i
    refine ⟨W.pushCh (f : Λ.Λ →+* R) ψ, ⟨pf_cont f hψ.cont, fun g => (res_map f _).trans (hψ.red g), fun g => ?_⟩, ?_⟩
    · show f (ψ g) = _
      rw [hψ.mu g, f.commutes]
    · exact congrArg (W.pushCh (f : Λ.Λ →+* R)) he
  have he : f = s := (Λ.univ R _ hi).unique (fun _ _ => rfl) fun v i =>
    MonoidHom.ext fun g => Units.ext (hsf f _ (hf v i g)).symm
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 := hs _ ha
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h1
  exact ⟨a, he ▸ h1⟩
private theorem pf_int {Λ B : Type} [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (t : Λ →ₐ[O] B) (J : Ideal B)
    (hfin : ((Ideal.Quotient.mk J).comp (t : Λ →+* B)).Finite) (f : B →ₐ[O] R) (hJ : ∀ b ∈ J, f b = 0)
    (hc : ∀ x, ∃ a, f (t x) = algebraMap O R a) (b : B) : IsIntegral O (f b) := by
  obtain ⟨p, hp, hb⟩ := hfin.to_isIntegral (Ideal.Quotient.mk J b)
  have h1 := congrArg (Ideal.Quotient.lift J (f : B →+* R) hJ) hb
  rw [hom_eval₂, map_zero] at h1
  have hl : p.map ((f.comp t : Λ →ₐ[O] R) : Λ →+* R) ∈ lifts (algebraMap O R) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := hc (p.coeff n)
    exact ⟨a, by rw [coeff_map]; exact ha.symm⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hm, ?_⟩
  rw [← eval_map, hq, eval_map]
  exact h1
variable {O₀ Γ : Type} [CommRing O₀] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O₀ Γ} {a : O₀ →+* O} (X : Space Φ a)
private theorem pf_sq (f : X.B →ₐ[O] R) (g : Γ) (hg : ∀ n, IsIntegral O (f ((X.cp (g ^ 2)).coeff n))) (n : ℕ) :
    IsIntegral O (f ((X.cp g).coeff n)) := by
  let S₀ : Subring X.B := (integralClosure O R).toSubring.comap (f : X.B →+* R)
  let S : Subring X.A := S₀.map (algebraMap X.B X.A)
  have h1 := AlgebraTools.charpolyPowInt X.A (Fin 4) S (X.P.r g) 2 two_pos (fun i => by
    rw [← map_pow, ← X.cp_map, coeff_map]
    exact ⟨_, hg i, rfl⟩) n
  rw [← X.cp_map, coeff_map] at h1
  obtain ⟨p, hp, hb⟩ := h1
  have hl : p.map S.subtype ∈ lifts ((algebraMap X.B X.A).comp S₀.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro m
    obtain ⟨y, hy, he⟩ := (p.coeff m).2
    exact ⟨⟨y, hy⟩, by rw [coeff_map]; exact he⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  have h2 : q.eval₂ S₀.subtype ((X.cp g).coeff n) = 0 := by
    apply X.inj
    rw [hom_eval₂, map_zero, ← eval_map, hq, eval_map]
    exact hb
  let j : S₀ →+* integralClosure O R := ((f : X.B →+* R).comp S₀.subtype).codRestrict _ fun y => y.2
  have h3 : IsIntegral (integralClosure O R) (f ((X.cp g).coeff n)) := by
    refine ⟨q.map j, hm.map j, ?_⟩
    have h4 := congrArg (f : X.B →+* R) h2
    rw [hom_eval₂, map_zero] at h4
    rw [eval₂_map]
    exact h4
  exact isIntegral_trans _ h3
private theorem pf_gen [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : X.B →ₐ[O] R)
    (h1 : ∀ g n, IsIntegral O (f ((X.cp g).coeff n))) (h2 : ∀ v i, ∀ s ∈ Φ.Gv v, IsIntegral O (f (X.ψ v i s))) :
    ∀ b ∈ maximalIdeal X.B, f b = 0 := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 X.B
  rw [X.genB R f s (fun g n => hsf f _ (pf_const h0 (h1 g n))) fun v i g hg => hsf f _ (pf_const h0 (h2 v i g hg))]
  exact hs
private theorem pf_unit {u : Oˣ} {y : R} (h : IsIntegral O (algebraMap O R u * y)) : IsIntegral O y := by
  have h1 := (isIntegral_algebraMap (R := O) (A := R) (x := (u⁻¹ : Oˣ))).mul h
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h1
end Abstract
section Galois
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)
private theorem pf_lift {g : G T.F Ω} (hg : resQ T.F g ∈ T.K.fixingSubgroup) : ∃ g' : G T.L Ω, resLe T.F_le g' = g := by
  have h1 : resQ T.F g ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have h2 : resQ T.F g ∈ T.L.fixingSubgroup := by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, hg⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at h2
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h2 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩
private theorem pf_sqK (g : G ℚ Ω) : g ^ 2 ∈ T.K.fixingSubgroup := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsGalois ℚ Ω := inferInstance
  have hi : T.K.fixingSubgroup.index = 2 := by
    rw [← T.degK]
    exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω T.K).symm
  exact Subgroup.sq_mem_of_index_two hi g
end Galois
theorem UpperTheory.V.Ws.exists_pow_maximalIdeal_le_of_modular_phi :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
        Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1} := by
  intro _ Ω _ _ _ l _ c D T hT _ c' h K X B Λ ι J₀ hM φ hφ J hJ
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq, hp⟩
  have hl : l ∈ D.S := hT.2.elim (fun x => x.1.1.l_mem) fun x => x.1.1.l_mem
  let π : X.B →ₐ[c'.O] X.B ⧸ q := Ideal.Quotient.mkₐ c'.O q
  haveI : IsCO c'.O (X.B ⧸ q) := co_quot c'.O X.B _ π Ideal.Quotient.mk_surjective
  have hπ : ∀ b, π b = 0 ↔ b ∈ q := fun b => Ideal.Quotient.eq_zero_iff_mem
  have h0 : ∀ a ∈ maximalIdeal c'.O, algebraMap c'.O (X.B ⧸ q) a = 0 := fun a ha => by
    rw [← π.commutes, hπ]
    exact hq (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))
  have hone : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), π (X.ψ v i s) = 1 := fun v i s hs => by
    rw [← sub_eq_zero, ← map_one π, ← map_sub, hπ]
    exact hq (Ideal.mem_sup_right (Ideal.subset_span ⟨v, i, s, hs, rfl⟩))
  have hΛ := pf_lam Λ h0 ((π.comp φ).comp (Λ.toPair B.u)) fun v i g => by
    have h1 : Λ.toPair B.u (Λ.κ v i g) = B.u.ψ v i g :=
      congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec K.r Λ B.u v i) g)
    refine ⟨K.κ g.1.1 * K.β g.1.1 ^ 0, ?_⟩
    have h2 : resLe T.F_le g.1.1 ∈ Ine (F := T.F) (T.pl (K.e v)) :=
      (congrArg (fun A => resLe T.F_le g.1.1 ∈ Ine (F := T.F) A) (K.hA v)).mp g.2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, hφ.2 v i g.1, map_mul, π.commutes, hone _ _ _ h2, mul_one]
  have hB := pf_int (Λ.toPair B.u) J₀ hM.ring.fin (π.comp φ) (fun b hb => by
    rw [AlgHom.comp_apply, hπ]
    exact hq (Ideal.mem_sup_left (Ideal.mem_sup_left (hJ ▸ Ideal.mem_map_of_mem _ hb)))) hΛ
  intro b hb
  rw [← hπ]
  refine pf_gen X h0 π (fun g => pf_sq X π g fun n => ?_) (fun v i s hs => ?_) b hb
  · obtain ⟨g', hg'⟩ := pf_lift T (g := g ^ 2) (by rw [map_pow]; exact pf_sqK T _)
    have h1 := hB ((B.u.D.chi (MonoidAlgebra.single (K.V.pr g') 1)).coeff n)
    have h2 := congrArg (fun p => p.coeff n) (hφ.1 g')
    simp only [coeff_map, coeff_scaleRoots, hg'] at h2
    rw [AlgHom.comp_apply] at h1
    erw [h2] at h1
    rw [map_mul, map_pow, π.commutes, mul_comm, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← Units.val_pow_eq_pow_val] at h1
    exact pf_unit h1
  · obtain ⟨v, rfl⟩ := K.e.surjective v
    obtain ⟨g', rfl⟩ := pf_lift T (g := s) (hT.1.split l hl _ (T.ovl (K.e v)) hs)
    have hg : g' ∈ Dec (F := T.L) (K.s.A v) := by
      rw [K.hA]
      exact hs
    have h1 := hB (B.u.ψ v i ⟨g', hg⟩)
    rw [AlgHom.comp_apply, hφ.2 v i ⟨g', hg⟩, map_mul, π.commutes, ← Units.val_pow_eq_pow_val, ← Units.val_mul] at h1
    exact pf_unit h1
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
attribute [local instance high] DivisionSemiring.to_moduleIsTorsionFree
theorem UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (k : Type) [Field k] [Finite k] [Algebra c'.O k] (y : X.A →ₐ[c'.O] PowerSeries k),
        (∀ b ∈ maximalIdeal X.B, PowerSeries.constantCoeff (y (algebraMap X.B X.A b)) = 0) →
        (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        (∀ v i j, i ≠ j → ∃ s ∈ T.U1 v, y (X.P.ψ v i s) ≠ y (X.P.ψ v j s)) →
        Irr (mapRep ((algebraMap (PowerSeries k) (FractionRing (PowerSeries k))).comp (y : X.A →+* PowerSeries k)) X.P.r) →
        X.LocZero J (y : X.A →+* PowerSeries k) := by
  intro _ Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ k _ _ _ y hy hyJ hU hI q hq hqy
  have hQ := P1.psPair D T c' h X k y hy
  haveI : IsLocalHom (algebraMap c'.O k) := ⟨fun a ha => by
    by_contra hn
    exact ha.ne_zero (hQ.loc a hn)⟩
  letI : Algebra (ResidueField c'.O) k := (ResidueField.lift (algebraMap c'.O k)).toAlgebra
  haveI : IsScalarTower c'.O (ResidueField c'.O) k := IsScalarTower.of_algebraMap_eq fun a => rfl
  obtain ⟨hfin, hchar, -⟩ := P1.coefRes c'
  obtain ⟨ρ, hρ, hρc⟩ := P1.rhoEx D T c' h K (PowerSeries k) _ (maximalIdeal _) (fun a ha => by
    rw [PowerSeries.algebraMap_apply, hQ.loc a ha, map_zero]; exact zero_mem _) hQ.pair hQ.cont
  obtain ⟨P, hP, hform⟩ := P1.formEx D T hF hD c' h K _ _ ρ hQ.pair hρ
  obtain ⟨ψ, hψ, hflag⟩ := P1.psiEx D T c' h K _ _ ρ hQ.pair hρ
  obtain ⟨hψr, hψc⟩ := P1.redPsi D T c' h K k _ hQ ψ hψ
  let x : W.Point K.r :=
    { K := k, ρ := ρ, cont := hρc, P := P, symm := hP, form := hform, red := P1.redDet D T c' h K k _ hQ ρ hρ
      ine := P1.ineTriv D T c' h K _ _ ρ hQ.pair hρ, ψ := ψ, ψ_red := hψr, flag := fun v => hflag _ _ v }
  obtain ⟨hne, hA⟩ := P1.condA D T hF hD c' h K _ _ ψ hψ (fun v i j hij => by
    obtain ⟨s, hs, hne⟩ := hU v i j hij
    have e := (sxPdMap (Φ := T.fr ∅) ((algebraMap c'.O X.A).comp (inc h)) (y : X.A →+* PowerSeries k) X.P).1
    exact ⟨s, hs, fun hh => hne ((e v i s).symm.trans (hh.trans (e v j s)))⟩)
  obtain ⟨n1, n2, n3⟩ := h4 l K.s.odd K.V.frame c'.O K.r x hne hψc hA
    (P1.irrL D T c' h K x _ hQ hρ hI) (P1.condC D T hF hD c' h K) (P1.condD D T hF hD c' h K)
  let f : B.B →ₐ[c'.O] x.A := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hf : B.IsPt x f := P1.mapsPt D T c' h K X B φ hφ _ y ρ ψ hρ hψ
  have key := hM.p1 x f ⟨n1, n2, n3, P1.n4V0 l _ _ 4 K.r K.v0 x⟩ hf
    (fun b hb => hyJ _ (hJ ▸ Ideal.mem_map_of_mem φ hb)) ⟨q.comap φ, hq.comap φ⟩ (fun b hb => hqy _ hb)
  rw [hJ]
  exact Ideal.map_le_iff_le_comap.2 key
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, (∀ b ∈ J, y (algebraMap X.B X.A b) = 0) →
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN K.s.v0 ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X B Λ ι J₀ hM φ hφ J hJ y hy hW r hr hc hm hi
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  let x : B.Pt := (y.comp (IsScalarTower.toAlgHom c'.O X.B X.A)).comp φ
  have hx : ∀ b, x b = y (algebraMap X.B X.A (φ b)) := fun _ => rfl
  have hJx : J₀ ≤ RingHom.ker x := fun b hb => hy _ (hJ ▸ Ideal.mem_map_of_mem φ hb)
  have hrL : (X.P.map (y : X.A →+* PadicAlgCl l)).r.comp (resLe T.F_le) = r.comp (resQ T.L) := by
    rw [← hr]; rfl
  have hcL : Continuous (r.comp (resQ T.L)) := hc.comp (Af.continuous_restrictScalarsHom _ _ _)
  have hanti : StrictAnti fun i => (D.wts4 i : ℤ) := by
    have := hG.two_le
    refine Fin.strictAnti_iff_succ_lt.2 fun i => ?_
    fin_cases i <;> simp [Raw.wts4] <;> omega
  obtain ⟨w, hw⟩ := auArith U.pr.toClassicalTheorems.litN.aut.art D T c' h K X B φ hφ y x hx
    (auPsiCont D T c' h K X B 0 φ hφ y x hx (hrL ▸ hcL)) _ hanti hW
  have hrep := auRep D T c' h K X B 0 φ hφ y x hx
  rw [hrL, pow_zero, mul_one] at hrep
  obtain ⟨hi1, hi2⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN K.v0 hM.end2 x w _ hJx hw hrep (hi2 _)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (ι : PadicAlgCl l ≃+* ℂ), Af.IsAlgChar ι (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := by
  intro hP Ω _ _ _ l _ c D T c' h K ι
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ (auCont c' K.κ K.κ_cont) fun w hw => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
    rwa [e] at h1
  obtain ⟨a, b, k, hk, -, H⟩ := K.cyc A hl
  refine ⟨A, hA, a, k, hk, fun s hs => ?_⟩
  rw [← (auChi T.L Ω c').1]
  have h2 := congrArg (Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom) (H s hs).1
  rw [map_pow, map_mul, map_zpow, map_one] at h2
  exact h2
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.ofOne0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → Third → Across → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure ℚ Ω], Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    ∀ (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ), IsAlgChar ι θ → DualTw r θ →
    IsIrr (r.comp (resG ℚ K Ω)) → IsAut ι (r.comp (resG ℚ K Ω)) → IsAutomorphicOverImagQuad ι r := by
  intro hP hT hA K Ω _ _ _ _ _ _ _ _ hK l _ ι n hn r θ hθ hd hirr haut hc K' _ _ _ inst _ tow hK' hirr'
  obtain rfl : inst = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨K'', _, _, _, _, _, hK'', h1, h2⟩ := hT K K' Ω hK hK' l n r hirr hirr'
  have h3 := hA K K'' Ω hK hK'' l ι n hn r θ hc hθ hd h1 haut
  rw [inf_comm] at h2
  have h4 := hA K'' K' Ω hK'' hK' l ι n hn r θ hc hθ hd h2 h3
  exact (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP K' Ω l ι n _).2.1.1 h4
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
open scoped Matrix
private theorem across_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem across_pair {F₀ F Ω k : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [Field k] {n : ℕ} (r : G F₀ Ω →* GL (Fin n) k) (θ : G F₀ Ω →* kˣ) (h : DualTw r θ)
    (c : G F₀ Ω) : ∃ P, IsPairing c (r.comp (resG F₀ F Ω)) (θ.comp (resG F₀ F Ω)) P := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : resG F₀ F Ω s' = c * resG F₀ F Ω s * c⁻¹ := h
  have e : r c⁻¹ * r (resG F₀ F Ω s') = r (resG F₀ F Ω s) * r c⁻¹ := by
    rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r (resG F₀ F Ω s')).val = (r (resG F₀ F Ω s)).val * (r c⁻¹).val := congrArg Units.val e
  have hp := hJ (resG F₀ F Ω s)
  simp only [MonoidHom.comp_apply]
  rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem across_tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] across_tf
private theorem across_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
private theorem across_irr {Γ Δ Δ' k : Type} [Group Γ] [Group Δ] [Group Δ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (f : Δ →* Γ) (f' : Δ' →* Γ) (h : ∀ s, ∃ t, f' t = f s) (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
  refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
  obtain ⟨t, ht⟩ := h s
  have := hI t v hv
  rw [MonoidHom.comp_apply, ht] at this
  exact this
theorem UpperTheory.V.Z.Bc.across_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → SolC → BiQuad → Across := by
  intro _ hS hB K K' Ω _ _ _ _ _ _ _ iA _ _ iT iT' iC hK hK' l _ ι n hn r θ hr hθ hd hirr haut
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨M, _, _, iM, _, _, _, _, _, _, _, hs, hs', hM, -⟩ := hB K K' Ω hK hK'
  haveI := across_up K Ω
  haveI := across_up K' Ω
  haveI := across_up M Ω
  obtain ⟨c, hc⟩ := across_cc Ω
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have hi : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine across_irr r _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hirr
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  obtain ⟨P, hP⟩ := across_pair (F := K) r θ hd c
  obtain ⟨P', hP'⟩ := across_pair (F := K') r θ hd c
  have h1 := (hS ℚ K M Ω hs ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P, hc, hP⟩).1 haut
  rw [he] at h1 hi
  exact (hS ℚ K' M Ω hs' ⟨inferInstance, Or.inr ⟨hK', inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K' Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P', hc, hP'⟩).2 h1
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private cc_ex from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.CcEx
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
theorem UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr (H : _root_.UpperTheory.V.Af.HypothesesH') (hS : SolC) (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (K L : IntermediateField ℚ Ω) [NumberField K] [NumberField L] [IsCMField K] [IsCMField L] (hle : K ≤ L)
    (hK : Module.finrank ℚ K = 2) (hgal : IsGalois ℚ L) (hsol : IsSolvable (L ≃ₐ[ℚ] L)) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (hn : 1 ≤ n) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (θ : G ℚ Ω →* (Qbar l)ˣ) (hr : Continuous r) (hθ : IsAlgChar ι θ)
    (hd : DualTw r θ) (hirr : IsIrr (r.comp (resG ℚ L Ω))) (haut : IsAut ι (r.comp (resG ℚ L Ω))) : IsAutomorphicOverImagQuad ι r := by
  letI : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) := hsol
  have s2 : IsSolvable (L ≃ₐ[K] L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.comp (resG ℚ K Ω)).comp (resG K L Ω) = r.comp (resG ℚ L Ω) := rfl
  have i2 : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K L Ω)) := e ▸ hirr
  have i1 : IsIrr (r.comp (resG ℚ K Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ i2
  obtain ⟨c, hc⟩ := cc_ex Ω
  obtain ⟨P, hP⟩ := id hd
  have hp : IsPairing c (r.comp (resG ℚ K Ω)) (θ.comp (resG ℚ K Ω)) (P * r c⁻¹) := fun s s' h => by
    have h' : resG ℚ K Ω s' = c * resG ℚ K Ω s * c⁻¹ := h
    have e0 : r c⁻¹ * r (resG ℚ K Ω s') = r (resG ℚ K Ω s) * r c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
    have e' := congrArg Units.val e0
    have h1 := hP (resG ℚ K Ω s)
    simp only [Units.val_mul, MonoidHom.comp_apply] at e' ⊢
    rw [← Matrix.smul_mul, ← h1]
    simp only [Matrix.mul_assoc, e']
  refine _root_.UpperTheory.GalN.V.ofOne0_alt H third (_root_.UpperTheory.V.Z.Bc.across_alt H hS biQuad) K Ω hK l ι n hn r θ hθ hd i1 ?_
  exact (hS ℚ K L Ω s2 ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance inferInstance l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) i2 hθ (Ws.auSign _) ⟨c, _, hc, hp⟩).2 (e ▸ haut)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Z.Win in
theorem UpperTheory.V.Z.Win.Dn.pmDown_alt :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (ι : PadicAlgCl l ≃+* ℂ) (y : X.A →ₐ[c'.O] PadicAlgCl l),
        T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) →
        ∀ r : G ℚ Ω →* M4 (PadicAlgCl l), r.comp (resQ T.F) = (X.P.map (y : X.A →+* PadicAlgCl l)).r → Continuous r → D.Mult r →
          Irr (r.comp T.L.fixingSubgroup.subtype) → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)) → _root_.UpperTheory.V.Aut.IsAut4Alt ι r := by
  intro U Ω _ _ _ l _ c D T hF _ c' h K X ι y hW r hr hc hm hi h1
  have hG : D.Good := hF.2.elim (fun a => a.1.1) (fun a => a.1.1)
  obtain ⟨hi1, -⟩ := auIrr _ (r.comp (resQ T.L)) hi fun g =>
    ⟨IntermediateField.fixingSubgroupEquiv T.L g, rfl⟩
  have h2 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida U.pr T.L Ω l ι 4 _).2.2 h1
  have hκ := _root_.UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa U.pr D T c' h K ι
  have hN := _root_.UpperTheory.GalN.V.csdN'_alt U.pr.toClassicalTheorems (by norm_num) h1
  have hκc : Continuous (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := hκ.choose_spec.1
  have hcr : Continuous r.toHomUnits := Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩
  have hW3 := _root_.UpperTheory.V.Z.Win.Dn.twist'_alt U.pr.toClassicalTheorems ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2 hκc.inv
    (hN.2 (Af.Bc.irrBasic.2 _ _ _ _ _ (hcr.comp (Af.continuous_restrictScalarsHom ℚ T.L Ω)) hκc))
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic U.pr T.L Ω l ι 4 _ _ h2 ((_root_.UpperTheory.V.Af.algOfCyc_s U.pr T.L Ω l ι).2.1 _ _ hκ hκ).2
  have h4 : Af.tw (Af.tw (r.comp (resQ T.L)).toHomUnits (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ))
      (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ)⁻¹ = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
    rfl
  rw [h4] at h3 hW3
  obtain ⟨hgal, hsol⟩ := auGal D T
  obtain ⟨P, hP⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm 1
  have h0 := _root_.UpperTheory.GalN.V.isAutomorphicOverImagQuad_of_restriction_aut_irr U.pr (Z.Bc.solC_of_solDescent (_root_.UpperTheory.V.Af.solvable_descent_of_printed_hida U.pr)) Ω T.K T.L (T.hL ▸ le_sup_right) T.degK hgal hsol l ι 4
    (by norm_num) r.toHomUnits (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th)
    (Units.continuous_iff.2 ⟨hc, hc.comp continuous_inv⟩) (_root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι)
    ⟨P, fun s => by simpa using hP s⟩ hi1 h3
  obtain ⟨hI, hFl, hU⟩ := UpperTheory.V.Keep.ptLaws D T hG hF.1 hF.1.locL c' h X y hW r hr
  have hle : T.K ≤ T.L := T.hL ▸ le_sup_right
  letI : Algebra T.K T.L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower T.K T.L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚ T.K T.L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  haveI : IsGalois T.K T.L := IsGalois.tower_top_of_isGalois ℚ T.K T.L
  haveI : Group.IsSolvable (T.L ≃ₐ[ℚ] T.L) := hsol
  have s2 : Group.IsSolvable (T.L ≃ₐ[T.K] T.L) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom ℚ : (T.L ≃ₐ[T.K] T.L) →* (T.L ≃ₐ[ℚ] T.L)))
      (AlgEquiv.restrictScalars_injective ℚ)
  have e : (r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω) = r.toHomUnits.comp (Af.resG ℚ T.L Ω) := rfl
  have i2 : Af.IsIrr ((r.toHomUnits.comp (Af.resG ℚ T.K Ω)).comp (Af.resG T.K T.L Ω)) := e ▸ hi1
  have i1 : Af.IsIrr (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := (Af.Bc.irrBasic.1 _ _ _ 4 _).1 _ i2
  have hcK : Continuous (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) := hcr.comp (Af.continuous_restrictScalarsHom ℚ T.K Ω)
  obtain ⟨Q, hQ⟩ := auPair r (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) hm D.cc
  have hpol : Af.Sol.Pol ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    ⟨ℚ, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, _, D.cc, Q, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, auSign _, hG.isCC, fun s s' h => by
        have h' : Af.resG ℚ T.K Ω s' = D.cc * Af.resG ℚ T.K Ω s * D.cc⁻¹ := h
        rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h']
        exact hQ _⟩
  have fl := (flagLaws ℚ Ω l 4 r.toHomUnits).2.2.2 T.K
  have hWK : _root_.UpperTheory.V.Z.Win.WitA ι (r.toHomUnits.comp (Af.resG ℚ T.K Ω)) :=
    _root_.UpperTheory.V.Z.Win.Dn.down'_alt T.L U.pr s2 (by norm_num) hcK i2 hpol (h0 hcr T.K T.degK i1) (fl.2.1 hFl) (fl.1 hI) (fun w hw _ => hU w hw) (e ▸ hW3)
  exact _root_.UpperTheory.GalN.V.isAutQA_of_isAutomorphicOverImagQuad_of_witAQ h0 fun _ => _root_.UpperTheory.V.Z.Win.Dn.across'_alt U.pr T.K Ω T.degK (by norm_num)
    (fun A hA g hg x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hF.1.split l hG.l_mem A hA hg) x x.2) hcr h0
    ⟨_, _root_.UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good U.pr D hG ι, P, fun s => by simpa using hP s⟩ hI hFl i1 hWK
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.promodular_existence_of_local_zero (U : _root_.UpperTheory.V.Ws.UnramifiedInputs)
    (hS : ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
      X.LocZero J (y : X.A →+* PadicAlgCl l)) : _root_.UpperTheory.V.Ws.PMExAlt := by
  intro Ω _ _ _ l _ c D T hF hD ι
  obtain ⟨c₁, hc₁⟩ := _root_.UpperTheory.Gal.projectedFormsSystemPart.exists_two_links_same_kappa_not_dvd_of_fit_deep U D T hF hD
  refine ⟨c₁, fun c' h h₁ X => ?_⟩
  obtain ⟨K, K', hκ, hp⟩ := hc₁ c' h h₁
  obtain ⟨⟨B, -⟩, hφ⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link U D T hF hD c' h K X 0
  obtain ⟨φ, hφ⟩ := hφ B
  obtain ⟨Λ, -⟩ := U.lam l T.L Ω K.s K.V c' 4 K.r
  obtain ⟨J₀, hJ⟩ := U.modU l T.L Ω K.s K.V K.hV K.noMu c' K.large 4 (by norm_num) K.r B Λ ι
  obtain ⟨⟨B', -⟩, hφ'⟩ := _root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link U D T hF hD c' h K' X 0
  obtain ⟨φ', hφ'⟩ := hφ' B'
  obtain ⟨Λ', -⟩ := U.lam l T.L Ω K'.s K'.V c' 4 K'.r
  obtain ⟨J₀', hJ'⟩ := U.modU l T.L Ω K'.s K'.V K'.hV K'.noMu c' K'.large 4 (by norm_num) K'.r B' Λ' ι
  have hl : ∀ {b}, b ∈ J₀.map φ → b ∈ J₀.map φ ⊔ J₀'.map φ' := fun hb => Ideal.mem_sup_left hb
  have hr : ∀ {b}, b ∈ J₀'.map φ' → b ∈ J₀.map φ ⊔ J₀'.map φ' := fun hb => Ideal.mem_sup_right hb
  refine ⟨J₀.map φ ⊔ J₀'.map φ', ?_, fun k _ _ _ y y1 y2 y3 y4 q hq hy => sup_le ?_ ?_, fun y y1 q hq hy => sup_le ?_ ?_,
    fun y y1 => _root_.UpperTheory.V.Ws.pmPur_w_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y fun b hb => y1 b (hl hb),
    fun y y1 y2 r r1 r2 r3 r4 => ?_⟩
  · obtain ⟨n, hn⟩ := _root_.UpperTheory.V.Ws.exists_pow_maximalIdeal_le_of_modular_phi U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl
    exact ⟨n, hn.trans (sup_le_sup_right (sup_le_sup_right le_sup_left _) _)⟩
  · exact _root_.UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl k y y1 (fun b hb => y2 b (hl hb)) y3 y4 q hq hy
  · exact _root_.UpperTheory.V.Ws.modular_deformation_quotient_regular_at_point_alt U D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl k y y1 (fun b hb => y2 b (hr hb)) y3 y4 q hq hy
  · exact hS D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y y1 q hq hy
  · exact hS D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl y y1 q hq hy
  · have a := _root_.UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt U D T hF hD c' h K X B Λ ι J₀ hJ φ hφ _ rfl y (fun b hb => y1 b (hl hb)) y2 r r1 r2 r3 r4
    have b := _root_.UpperTheory.Gal.projectedFormsSystemPart.pmAutO_alt U D T hF hD c' h K' X B' Λ' ι J₀' hJ' φ' hφ' _ rfl y (fun b hb => y1 b (hr hb)) y2 r r1 r2 r3 r4
    rw [hκ] at b
    exact _root_.UpperTheory.V.Z.Win.Dn.pmDown_alt U D T hF hD c' h K X ι y y2 r r1 r2 r3 r4
      (_root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (UpperTheory.Gal.projectedFormsSystemPart.v0_ne hp) a b)
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private half_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.HalfPow
open UpperTheory.GalN.V UpperTheory.V.Ws.Pt UpperTheory.V.Z.Win
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp Formalism.BasicNotions Formalism.MainNotions.N
namespace UpperTheory.V.Z.Win.Birth
theorem ptAutR'_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (n : ℕ) (ι : PadicAlgCl l ≃+* ℂ) (r : G T.F Ω →* M4 (PadicAlgCl l)), (∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g)))) (r g)) → ∀ (κ : G T.L Ω →* (PadicAlgCl l)ˣ) (π : CuspSub T.L 4) (a : ℤ) (k : ℕ), Continuous κ → 0 < k → Even (a + n) → (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := T.L) A, (κ s ^ 2 * cycBar T.L Ω l s ^ (-a)) ^ k = 1) → CuspidalRankFourRegularAlgebraicTotallyComplex π → Af.AttC ι (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) π → (∀ w : HeightOneSpectrum (𝓞 T.L), ((l : ℕ) : 𝓞 T.L) ∈ w.asIdeal → PotUnl (K.rhoQ n r) w) → IsAutCsdA ι (K.rhoQ n r) := by
  intro hP Ω _ _ _ l _ c D T c' h K n ι r hr κ π a k hκ hk ha hw ⟨hreg, hwin⟩ hatt hpot
  have h1 := (_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP T.L Ω l ι 4 _).2.1.2 ⟨π, hreg, hatt⟩
  have h2 : Af.IsAlgChar ι (K.twc n * κ⁻¹) := by
    refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ ((twc_cont K n).mul hκ.inv) fun w hlw => ?_
    obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    have hl : A.valuation (l : Ω) < 1 := by
      have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hlw
      have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
      rwa [e] at h1
    obtain ⟨e, k', hk', he, H⟩ := twWts K n A hl
    obtain ⟨m, hm⟩ : Even (e - a) := by
      have := he.sub ha
      rwa [add_sub_add_right_eq_sub] at this
    exact ⟨A, hA, m, 2 * (k * k'), by positivity, fun s hs => half_pow hm (H s hs) (hw A hl s hs)⟩
  have h3 := _root_.UpperTheory.V.Af.twist_invariance_automorphic hP T.L Ω l ι 4 _ _ h1 h2
  have h4 : Af.tw (Af.tw (r.comp (resLe T.F_le)).toHomUnits κ) (K.twc n * κ⁻¹) = K.rhoQ n r := by
    ext g : 2
    rw [Af.tw_val, Af.tw_val, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.inv_mul_cancel_right, K.rho_val]
    rfl
  rw [h4] at h3
  obtain ⟨P, hPair⟩ := ptPair K n r hr
  haveI : IsAlgClosure T.L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  have h5 : Sd.IsAlgChar ι (K.twc n * κ⁻¹) := by
    obtain ⟨χ, hc, art, a', b1, b2, b3⟩ := h2
    exact ⟨hc, art, χ, a', b1, b2, b3⟩
  have h6 := awTw T.L Ω l 4 (by norm_num) ι _ _ h5 ⟨π, hreg, hatt⟩ (awOne T.L Ω l 4 (by norm_num) ι _ π hatt hwin)
  rw [h4] at h6
  exact ⟨_root_.UpperTheory.GalN.V.csdOf0_alt hP (W.Lp T.L) T.L Ω inferInstance l ι 4 (by norm_num) _ K.s.c P K.s.hc h3 hPair, fun _ => h6.witA hpot⟩
end UpperTheory.V.Z.Win.Birth
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.Pt.point_representation_weights :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : W.Resid V.frame c.O n) (B : W.UniversalOrdinaryDeterminantRing r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.PointTheoremBaseObject ι J → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)) (m : W.Vl l L → Fin n → ℤ), 2 ≤ n → n ≤ 4 → x.IsRep ρ → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → (∀ v i j, i < j → m v j + 2 ≤ m v i) → (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) → (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) → J ≤ RingHom.ker x := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι J hJ x ρ m hn2 hn4 hrep hc haut hv0 hm hfl ⟨k, hk, hw⟩
  have hov : ∀ v : W.Vl l L, (s.A v).valuation (l : Ω) < 1 := fun v => by
    simpa using (s.hA v _).2 v.2
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using hov v
  refine hJ x (fun v j _ => -m v j) ρ hn2 hn4 ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
    hrep hc haut hv0
    fun v => ⟨hfl v, fun i j hij => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (psi_cont x v j) (m v j) k hk (hw v j)
  · have hne : 1 - m v i + m v j ≠ 0 := by
      rcases lt_trichotomy i j with h | h | h
      · have := hm v i j h
        omega
      · subst h
        omega
      · have := hm v j i h
        omega
    obtain ⟨g, hg, hg1⟩ := cycIne L Ω l (s.A v) (hov v) ((1 - m v i + m v j) * k)
      (mul_ne_zero hne (by exact_mod_cast hk.ne'))
    have hgD : g ∈ Dec (F := L) (s.A v) :=
      (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
    have h1 := hw v i ⟨g, hgD⟩ hg
    have h2 := hw v j ⟨g, hgD⟩ hg
    have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
      rw [hij]; rfl
    apply hg1
    have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
        (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
      rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
      congr 2
      ring
    change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
    change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
    rw [e2, mul_pow, h2, one_mul] at h1
    rw [zpow_mul, zpow_natCast, h1]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
open UpperTheory.V.Ws.H5 in
theorem UpperTheory.V.Ws.hida_modular_ideal_map :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ (n : ℕ) (φ' : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ' → J₀.map φ' = J := by
  intro _ Ω _ _ _ l _ c D T _ _ c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ'
  subst hJ
  have hl : ((l : ℕ) : B.B) ∈ maximalIdeal B.B := by
    haveI := (UpperTheory.V.Base.dvrFacts l c'.O).2.2.1
    have h1 : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
      rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have h2 := map_nonunit (algebraMap c'.O B.B) _ (map_nonunit (algebraMap ℤ_[l] c'.O) _ h1)
    simpa using h2
  have stab : ∀ γ : K.V.frame.G₀ →* B.Bˣ, TwCh K.V.frame γ → ∃ τ : B.B →ₐ[c'.O] B.B,
      TwMap B (RingHom.id B.B) (τ : B.B →+* B.B) γ ∧ ∀ b ∈ J₀, τ b ∈ J₀ := fun γ hγ => by
    obtain ⟨τ, hτ⟩ := twMapEx B (AlgHom.id c'.O B.B) γ hγ
    exact ⟨τ, hτ, fun b hb => closedJ _ J₀ _ (twJN B J₀ hM.dense hM.twist hl γ hγ τ hτ b hb)⟩
  have key : ∀ (γ : K.V.frame.G₀ →* c'.Oˣ), TwCh K.V.frame γ → ∀ f f' : B.B →ₐ[c'.O] X.B,
      TwMap B (f : B.B →+* X.B) (f' : B.B →+* X.B) (W.pushCh (algebraMap c'.O X.B) γ) → J₀.map f' ≤ J₀.map f := by
    intro γ hγ f f' hf
    obtain ⟨τ, hτ, hτJ⟩ := stab _ ((twChOps _ γ hγ).2.2 B.B (algebraMap c'.O B.B) inferInstance)
    have h1 := hτ.comp (f : B.B →+* X.B)
    have h2 : W.pushCh (f : B.B →+* X.B) (W.pushCh (algebraMap c'.O B.B) γ) = W.pushCh (algebraMap c'.O X.B) γ :=
      MonoidHom.ext fun g => Units.ext (f.commutes _)
    rw [h2, RingHom.comp_id] at h1
    have h3 : f' = f.comp τ := twMapUniq B _ _ f' (f.comp τ) hf h1
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, h3]
    exact Ideal.mem_map_of_mem _ (hτJ b hb)
  obtain ⟨β₀, hβ, hβ'⟩ := descend K
  have hn := (twChOps _ β₀ hβ).1 n
  have hT := phiTw K X B β₀ hβ' n φ φ' hφ hφ'
  refine le_antisymm (key _ hn φ φ' hT) (key _ (twChOps _ _ hn).2.1 φ' φ ?_)
  have hu : ∀ g, algebraMap c'.O X.B (((β₀ ^ n)⁻¹ g : c'.Oˣ) : c'.O) * algebraMap c'.O X.B (((β₀ ^ n) g : c'.Oˣ) : c'.O) = 1 :=
    fun g => by rw [← map_mul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one, map_one]
  refine ⟨fun g i hi => ?_, fun v i g => ?_⟩
  · rw [hT.1 g i hi, ← mul_assoc, ← mul_pow]
    erw [hu g]
    rw [one_pow, one_mul]
  · rw [hT.2 v i g, mul_assoc, mul_comm (_ : X.B) ((W.pushCh _ (β₀ ^ n)⁻¹ _ : X.Bˣ) : X.B)]
    erw [hu]
    rw [mul_one]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
open UpperTheory.V.Ws.Eb
private theorem tan_one {K H : Type} [CommRing K] [Group H] {n : ℕ} {ρ : H →* GL (Fin n) K} {y : H → Matrix (Fin n) (Fin n) K}
    {ρ' : H →* GL (Fin n) (DualNumber K)} (h : IsTan ρ y ρ') (g : H) (hg : ρ' g = 1) : y g = 0 := by
  have e1 := h g
  rw [hg] at e1
  have e2 : (ρ g : Matrix (Fin n) (Fin n) K) = 1 := by
    ext i j
    have := congrArg TrivSqZeroExt.fst (e1 i j)
    by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
  ext i j
  have := congrArg TrivSqZeroExt.snd (e1 i j)
  rw [e2, mul_one] at this
  by_cases h : i = j <;> simpa [Matrix.one_apply, h] using this.symm
private theorem at_l (hP : Loc.LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n}
    (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (hΛ : ∀ a, (x' (Λ.toPair B.u a)).snd = 0)
    {ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)} {y : F.G₀ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} {ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))}
    (hcont : Continuous ρ) (hy : y ∈ Z1 (Loc.adGL ρ)) (htan : IsTan ρ y ρ') {P : GL (Fin n) (PadicAlgCl l)}
    {R : Representation (PadicAlgCl l) F.Γ (Matrix (Fin n) (Fin n) (PadicAlgCl l))} (hR : IsAdExt F ρ P R)
    {z : F.Γ → Matrix (Fin n) (Fin n) (PadicAlgCl l)} (hzy : ∀ g : F.G₀, z g = y g) (v : F.Vl)
    (hfl : W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i))
    (m : Fin n → ℤ) (k : ℕ) (hm : ∀ i j, i < j → m j + 2 ≤ m i) (hk : 0 < k) (φ : F.Gv v →* Formalism.BasicNotions.Loc.GQ l)
    (hφ : Topology.IsOpenEmbedding φ) (h1 : ∀ g, φ g ∈ Loc.Iq l ↔ g ∈ F.Iv v)
    (h2 : ∀ i, ∀ g ∈ F.Iv v, (W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) g *
      Loc.cycA l l (PadicAlgCl l) (φ g) ^ (-m i)) ^ k = 1) :
    (fun g : F.Gv v => z (F.φ v g)) ∈ Loc.finiteCocycles φ (R.comp (F.η.ker.subtype.comp (F.φ v)) :
      Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) := by
  have e1 : (R.comp (F.η.ker.subtype.comp (F.φ v)) : Representation (PadicAlgCl l) (F.Gv v) (Matrix (Fin n) (Fin n) (PadicAlgCl l))) =
      Loc.adGL (ρ.comp (F.φ v)) := MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad _ X
  rw [e1]
  simp only [hzy]
  refine locL hP φ hφ (ρ.comp (F.φ v)) (hcont.comp (F.φ_cont v)) _
    ⟨hy.1.comp (F.φ_cont v), fun g h => ?_⟩ _ (htan.comp (F.φ v)) _ m k hfl hm hk fun i g hg => ⟨?_, h2 i g ((h1 g).1 hg)⟩
  · exact (congrArg y (map_mul _ g h)).trans (hy.2 _ _)
  · have e2 := congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) ⟨g, (h1 g).1 hg⟩)
    exact (congrArg (fun b => (x' b).snd) e2).symm.trans (hΛ _)
section
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
private theorem over_l (v : W.Vl l L) : (s.A v).valuation (l : Ω) < 1 := by
  simpa using (s.hA v _).2 v.2
private theorem arith (hP : _root_.UpperTheory.V.Af.HypothesesH') (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : x.Arith fun v j _ => -m v j := by
  have hl : ∀ v : W.Vl l L, ((l : ℕ) : 𝓞 L) ∈ (s.w v).asIdeal := fun v => by
    refine (s.hw v _).1 ?_
    simpa using over_l (s := s) v
  refine ⟨fun v τ i j hij => ?_, fun v j => ?_⟩
  · have := hm v i j hij
    simp only
    omega
  · exact UpperTheory.V.Loc.laArith hP.toClassicalTheorems.litN.aut.art (s.hw v) (hl v) _ (Ws.Pt.psi_cont x v j) (m v j) k hk (hw v j)
private theorem noRatio (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) (v : W.Vl l L) (i j : Fin n) :
    x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
  intro hij
  have hne : 1 - m v i + m v j ≠ 0 := by
    rcases lt_trichotomy i j with h | h | h
    · have := hm v i j h
      omega
    · subst h
      omega
    · have := hm v j i h
      omega
  obtain ⟨g, hg, hg1⟩ := Ws.Pt.cycIne L Ω l (s.A v) (over_l v) ((1 - m v i + m v j) * k)
    (mul_ne_zero hne (by exact_mod_cast hk.ne'))
  have hgD : g ∈ Dec (F := L) (s.A v) :=
    (GlobalTheory.WeilDeligne.Weil_le_Dec (s.hw v)) (GlobalTheory.WeilDeligne.ineIncl (s.hw v) ⟨g, hg⟩).2
  have h1 := hw v i ⟨g, hgD⟩ hg
  have h2 := hw v j ⟨g, hgD⟩ hg
  have e : x.psi v i ⟨g, hgD⟩ = x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g := by
    rw [hij]; rfl
  apply hg1
  have e2 : x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i) =
      (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) * cycBar L Ω l g ^ (1 - m v i + m v j) := by
    rw [e, mul_assoc, mul_assoc, ← zpow_add, ← zpow_one_add]
    congr 2
    ring
  change (x.psi v i ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v i)) ^ k = 1 at h1
  change (x.psi v j ⟨g, hgD⟩ * cycBar L Ω l g ^ (-m v j)) ^ k = 1 at h2
  rw [e2, mul_pow, h2, one_mul] at h1
  rw [zpow_mul, zpow_natCast, h1]
private theorem par (x : B.Pt) (m : W.Vl l L → Fin n → ℤ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Par x := fun v =>
  ⟨m v, k, fun i j h => by have := hm v i j h; omega, hk, fun i j g hg => by
    have e : x.psi v i g / x.psi v j g * cycBar L Ω l g ^ (m v j - m v i) =
        (x.psi v i g * cycBar L Ω l g ^ (-m v i)) / (x.psi v j g * cycBar L Ω l g ^ (-m v j)) := by
      rw [mul_div_mul_comm, div_eq_mul_inv (_ ^ (-m v i)), ← zpow_neg, ← zpow_add]
      congr 2
      ring
    rw [e, div_pow, hw v i g hg, hw v j g hg, div_one]⟩
private theorem free (hP : _root_.UpperTheory.V.Af.HypothesesH') (hn : 1 ≤ n) (ι : PadicAlgCl l ≃+* ℂ) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l))
    (m : W.Vl l L → Fin n → ℤ) (hρ : Continuous ρ) (haut : _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ) (hm : ∀ v i j, i < j → m v j + 2 ≤ m v i)
    (hfl : ∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) (k : ℕ) (hk : 0 < k)
    (hw : ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) →
      (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) : Free V.frame fun v => x.psi v := fun v : W.Vl l L => by
  obtain ⟨g, hg, hf⟩ := _root_.UpperTheory.V.Z.Win.RR.exists_cycZ_eq_one_freeRatios_of_ne_mul_cycBar hP L Ω l s.odd ι n hn ρ hρ haut (s.A v) (over_l v) (x.psi v) (m v) k (hfl v)
    (fun i j h => by have := hm v i j h; omega) hk (hw v) (noRatio x m hm k hk hw v)
  refine ⟨g, ?_, hf⟩
  have e : V.ε (toGS Ω V.S' (W.resP L Ω g)) = cycZ (W.Lp L) Ω l (W.resP L Ω g) := DFunLike.congr_fun V.hε _
  exact e.trans hg
end
theorem UpperTheory.V.Th.eigenbasis_rank_four :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : W.HidaSetting l L Ω) (V : s.Lev), V.S' = s.S → (¬ ∃ ζ : L, IsPrimitiveRoot ζ l) → ∀ (c : Coef l), W.Large L c → ∀ (r : W.Resid V.frame c.O 4) (B : W.UniversalOrdinaryDeterminantRing r) (Λ : W.LamObj r) (ι : PadicAlgCl l ≃+* ℂ) (J : Ideal B.B), B.HidaPropsAlt ι J Λ → r.V0ok → (∀ η : V.frame.G₀ →* (ResidueField c.O)ˣ, η ^ 2 = 1 → (V.frame.eps c.O (ResidueField c.O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) → (∃ i j, ∀ m : ℕ, 0 < m → m ≤ 4 → (r.chib i / r.chib j) ^ m ≠ 1) → ∀ (x : B.Pt) (ρ : G L Ω →* GL (Fin 4) (PadicAlgCl l)) (m : W.Vl l L → Fin 4 → ℤ), J ≤ RingHom.ker x → x.IsRep ρ → Continuous ρ →
          _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ρ → (∀ g ∈ Ine (F := L) (s.A s.v0), ρ g = 1) → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) → (∀ v i j, i < j → m v j + 2 ≤ m v i) →
          (∀ v : W.Vl l L, W.HasFlag (ρ.comp (Dec (F := L) (s.A v)).subtype) (x.psi v)) →
          (∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l L) i (g : Dec (F := L) (s.A v)), (g : G L Ω) ∈ Ine (F := L) (s.A v) → (x.psi v i g * cycBar L Ω l g ^ (-m v i)) ^ k = 1) →
          ∀ q : Ideal B.B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro hU hAd l _ L Ω _ _ _ _ _ _ s V hV hζ c hc r B Λ ι J hJ h0 hC hD4 x ρ m hJx hx hρ haut hv0 hirr hm hfl ⟨k, hk, hkk⟩
  obtain ⟨Λ', ⟨e'⟩⟩ := hU.lam l L Ω s V c 4 r
  obtain ⟨e₁⟩ := lamIso Λ' Λ
  obtain ⟨e, he⟩ : ∃ e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →ₐ[c.O] Λ.Λ, Function.Bijective e :=
    ⟨(e'.symm.trans e₁ :), (e'.symm.trans e₁).bijective⟩
  refine regOfTan c _ B.B ((Λ.toPair B.u).comp e) J ?_ (fun a ha b hb => ?_) x hJx fun x' hx' hΛ => ?_
  · exact hJ.ring.fin.comp (RingHom.Finite.of_surjective (e : MvPowerSeries (Fin (4 * Module.finrank ℚ (W.Lp L))) c.O →+* Λ.Λ) he.2)
  · exact hJ.ring.tf (e a) ((map_ne_zero_iff e he.1).2 ha) b hb
  have hΛ' : ∀ a, (x' (Λ.toPair B.u a)).snd = 0 := fun a => by
    obtain ⟨a, rfl⟩ := he.2 a
    exact hΛ a
  have hxx : (dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l)) = (x : B.B →+* PadicAlgCl l) := RingHom.ext hx'
  have hn1 : 1 ≤ 4 := by omega
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := factor V B x ρ hn1 hx hirr
  obtain ⟨ρ', y, hD', hred, hfull', hcont, hy, htan⟩ := liftRep B x' ρ₀ hn1 hfull (by rw [hxx, hD])
  obtain ⟨hO, hI⟩ := relKill B x' ρ' hfull' hD'
  obtain ⟨P', hP'⟩ := relForm B x' ρ' hfull' hD'
  obtain ⟨hP, hrel⟩ := cocRel V.frame c.O ρ₀ y ρ' P' htan hP'
  obtain ⟨R, hR⟩ := adExt V.frame c.O ρ₀ _ hfull hP
  obtain ⟨Z, hZ⟩ := hrel R hR
  obtain ⟨z, hz, hzy⟩ := cocExt V.frame ρ₀ _ R hfull hcont hR y hy Z hZ
  have hinj : ∀ v : V.frame.Vl, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    refine psiInj (s.A v.1) (s.w v.1) (s.hw v.1) ?_ (x.psi v) (m v) k
      (StrictAnti.injective fun i j h => by have := hm v i j h; omega) hk (hkk v)
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  have hfl₀ : ∀ v : V.frame.Vl, W.HasFlag (ρ₀.comp (V.frame.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i) := fun v => by
    rw [hxx]
    exact hfl v
  have hfl' : ∀ v : V.frame.Vl, W.HasFlag (ρ'.comp (V.frame.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i) := fun v =>
    flagDual _ _ (hinj v) (by rw [← hred] at hfl₀; exact hfl₀ v) (hO v)
  have hbk := bkAb V R z hz
    (fun v φ hφ h1 h2 => at_l hU.coh.loc B Λ x' hΛ' hcont hy htan hR hzy v (hfl' v) (m v) k (hm v) hk φ hφ h1 fun i g hg => by
      rw [hxx, h2]
      exact hkk v i g hg)
    (bkAw V hV r R z hz (fun u g hg => (hzy g).trans (tan_one htan g (hI u g hg)))
      fun g hg => (hzy g).trans (cocycle_vanishes_on_inertia_of_point_pseudodeformation V B x ρ₀ h0 hD hcont y hy g hg))
  have hapt : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ₀ := ⟨hcont, hx, ⟨_, arith hU.pr x m hm k hk hkk⟩, haut, by
    rintro _ ⟨g, hg, rfl⟩
    exact hv0 g hg, hfl⟩
  have hirr₀ : U3.MatIrr ⊤ (W.mat ρ₀) := fun N hN => (AlgebraTools.Det.irrIffSpan (W.mat ρ₀)).2 hfull N fun g v hv => hN g trivial v hv
  have hnice := _root_.UpperTheory.V.Th.nice0four_alt ι x ρ₀ hapt hirr₀ (free hU.pr hn1 ι x _ m hρ haut hm hfl k hk hkk) hC hD4
  obtain ⟨X, hX⟩ := hAd l L Ω s V hV hζ c hc 4 (by omega) le_rfl r h0 B ι x ρ₀ hnice (par x m hm k hk hkk) _ R hP hR z hz hbk
  obtain ⟨Q, hQ⟩ := conjOf ρ₀ y ρ' X htan fun g => by rw [← hzy, hX, hR.ad]
  exact constOf B x' ρ₀ ρ' Q hD' hQ hinj hfl₀ hfl'
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Th
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
private theorem gsp_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {g : M4 R} (h : IsGSp ν g) :
    IsGSp (f ν) (g.map f) := by
  have a : adj (g.map f) = (adj g).map f := by
    ext i j
    simp only [adj_apply, Matrix.map_apply, map_zsmul]
  unfold IsGSp at h ⊢
  rw [a, ← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]
theorem UpperTheory.V.Th.local_zero_of_modular_p :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, T.IsSeedAlt ι (X.P.map (y : X.A →+* PadicAlgCl l)) →
        X.LocZero J (y : X.A →+* PadicAlgCl l) := by
  intro hU hA Ω _ _ _ l _ c D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ y hs q hq hqy
  obtain ⟨w, κ, π, a, k, hgap, hw, hκ, hk, hev, hκw, hreg, hatt⟩ := hs.aut
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Even (w 0 + n) := ⟨(w 0).natAbs, by
    rcases Int.natAbs_eq (w 0) with e | e <;> exact Int.even_iff.2 (by omega)⟩
  obtain ⟨d0, h0, e0⟩ := hgap 0
  obtain ⟨d1, h1, e1⟩ := hgap 1
  obtain ⟨d2, h2, e2⟩ := hgap 2
  replace e0 : w 0 = w 1 + 2 * d0 := e0
  replace e1 : w 1 = w 2 + 2 * d1 := e1
  replace e2 : w 2 = w 3 + 2 * d2 := e2
  rw [Int.even_iff] at hn hev
  obtain ⟨φ', hφ'⟩ := (_root_.UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link hU D T hF hD c' h K X n).2 B
  obtain ⟨m, hm, hmk⟩ := Pt.ptWts K X B n φ' hφ' y w (fun i => Int.even_iff.2 (by fin_cases i <;> simp <;> omega)) hw
  have hg : ∀ v i j, i < j → m v j + 2 ≤ m v i := fun v i j hij => by
    have := hm v i j
    fin_cases i <;> fin_cases j <;> simp at hij this ⊢ <;> omega
  obtain ⟨hi, hi'⟩ := Pt.ptIrr K n _ hs.irr
  have hc := Pt.rho_cont K n (Pt.pt_cont X y hi)
  have hrep : (Link.pt φ' y).IsRep (K.rhoQ n _) := auRep D T c' h K X B n φ' hφ' y _ fun _ => rfl
  have hmul : ∀ g, IsGSp (algebraMap c'.O (PadicAlgCl l) (inc h (D.th (resQ T.F g))))
      ((X.P.map (y : X.A →+* PadicAlgCl l)).r g) := fun g => by
    rw [← y.commutes]
    exact gsp_map (y : X.A →+* PadicAlgCl l) (X.pair.mult g)
  have hunr := Pt.ptUnr K n (X.P.map (y : X.A →+* PadicAlgCl l)).r fun g hg => by
    change (y : X.A →+* PadicAlgCl l).mapMatrix (X.P.r g) = 1
    rw [X.pair.kill g hg, map_one]
  have hfl := Pt.ptFlag K X B n φ' hφ' y
  obtain ⟨Pp, hPp⟩ := Pt.ptPair K n _ hmul
  have haut := _root_.UpperTheory.V.Z.Win.Birth.ptAutR'_alt hU.pr K n ι _ hmul κ π a k hκ hk (Int.even_iff.2 (by omega)) hκw hreg hatt
    (Z.ImaginaryQuadraticEtaCharacter.potOfPair l T.L Ω K.s 4 _ _ Pp hPp _ m hg hfl hmk)
  have hJx := _root_.UpperTheory.V.Ws.Pt.point_representation_weights hU.pr l T.L Ω K.s K.V c' 4 K.r B ι J₀ hM.pt _ _ m (by norm_num) (by norm_num) hrep hc haut hunr hg hfl hmk
  rw [← _root_.UpperTheory.V.Ws.hida_modular_ideal_map hU D T hF hD c' h K X B Λ ι J₀ hM φ hφ J hJ n φ' hφ', Ideal.map_le_iff_le_comap]
  exact _root_.UpperTheory.V.Th.eigenbasis_rank_four hU hA l T.L Ω K.s K.V K.hV K.noMu c' K.large K.r B Λ ι J₀ hM.toHidaProps K.v0 (P1.condC D T hF hD c' h K)
    (P1.condD D T hF hD c' h K) _ _ m hJx hrep hc haut hunr hi' hg hfl hmk
    _ (hq.comap φ') fun b hb => hqy _ hb
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.Gal.projectedFormsSystemPart.pm_exists_of_unramified_adjoint_lifting :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → _root_.UpperTheory.V.Th.AdjointLiftingTheorem → _root_.UpperTheory.V.Ws.PMExAlt := fun U hA => _root_.UpperTheory.Gal.projectedFormsSystemPart.promodular_existence_of_local_zero U (_root_.UpperTheory.V.Th.local_zero_of_modular_p U hA)
end
end
