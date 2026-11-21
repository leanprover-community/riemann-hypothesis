import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

section
set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing TG

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem isTheta_of_nonzeroOnSpecial' (hLaws : Laws) (hL4 : Laws4) (hR : CLND R)
    [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) : IsTheta U s := by
  have := flat_G U.toUnifPre
  have := flat_B (D := D)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hIϖ : I = Ideal.span {ϖ} := by
    rw [hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  obtain ⟨F, hF, -⟩ := (U.expand 1 le_rfl).1 (secK U.toUnifPre s)
  obtain ⟨r, hr0, σ, f, hσ, hfK, hexp⟩ := hF
  have hσr := sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  let τ : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (u : R)) s
  have hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j := fun j => by
    rw [hσr, hru]
    show _ = _ * (toW G.hom _ (u : R) * s.f j)
    rw [map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]
  obtain ⟨g, hfg, hexpg⟩ := expand_div_pow U.toUnifPre hL4.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp
  let g' : ∀ α, D.toPre.SecB 1 α := fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)
  have hexp' : ∀ e, U.ExpandsAt e 1 s g' := fun e =>
    expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by
      show _ = _ * (toW G.hom _ (u : R) * s.f j)
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)
  have hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
    intro α j₁ j₂ hc
    have e := hfK α j₁ j₂ hc
    have hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂ := by
      rw [hfg α j₂]
      show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)
      rw [← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    have hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
        (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
      simp [DegPre.BF, TF]
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e
    have hu := isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R))
      (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0
    rw [← toW_congr hBF] at hu
    have e2 := hu.mul_left_cancel e
    have h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂)
        (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 := map_one _
    rw [h1, _root_.one_mul]
    exact e2
  have hv := terms_vanish hϖ hI F g' hgF
  have h0 := leading_expansion_term_ne_zero hI U s hs g' (hexp' 0) hv
  exact fun e => ⟨g', hexp' e, generates_of_ne hLaws hI (g' 0) h0⟩

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing TG ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

section H0

variable {X : Scheme.{0}} {L : LB X}

theorem h0_le (j : Fin 1 → L.ι) : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun y hy => by
  simpa using Set.mem_iInter.1 hy 0

theorem chart_le_weighted_chart_single (i : L.ι) : L.U i ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) fun _ => i := fun y hy =>
  Set.mem_iInter.2 fun _ => by simpa using hy

theorem transition_factor_single_identity (y : X) (j j' : Fin 1 → L.ι) : trF (L := L) (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 X) y j j' =
    gm (𝟙 X) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) := by
  simp [trF]

def toH0 (θ : LB.Sec L) : H0 L 1 where
  f j := (X.presheaf.map (homOfLE (h0_le j)).op).hom (θ.f (j 0))
  compat j j' := fn_ext fun y hy => by
    have hm : (𝟙 X : X ⟶ X) y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ⊓ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j' := hy
    refine ((gs_res _ y inf_le_left hm _).trans (gs_res _ y (h0_le j) hm.1 _)).trans ((gs_compat θ _ y (h0_le j hm.1)
      (h0_le j' hm.2)).trans (Eq.symm ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
      (congrArg Units.val ((gm_linComb L _ _ (𝟙 X) y j j' hm.1 hm.2).trans (transition_factor_single_identity y j j'))))
      ((gs_res _ y inf_le_right hm _).trans (gs_res _ y (h0_le j') hm.2 _))))))

def secOfH0 (σ : H0 L 1) : LB.Sec L where
  f i := (X.presheaf.map (homOfLE (chart_le_weighted_chart_single i)).op).hom (σ.f fun _ => i)
  compat i i' := fn_ext fun y hy => by
    have hm : (𝟙 X : X ⟶ X) y ∈ L.U i ⊓ L.U i' := hy
    refine ((gs_res _ y inf_le_left hm _).trans (gs_res _ y (chart_le_weighted_chart_single i) hm.1 _)).trans ((sec_trans σ _ y (chart_le_weighted_chart_single i hm.1)
      (chart_le_weighted_chart_single i' hm.2)).trans (Eq.symm ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hm _).trans
      (congrArg Units.val (transition_factor_single_identity y (fun _ => i) fun _ => i').symm))
      ((gs_res _ y inf_le_right hm _).trans (gs_res _ y (chart_le_weighted_chart_single i') hm.2 _))))))

theorem ne_zero_of_gen {K : Type} [Field K] {p : X ⟶ Sp K} {b : LB.Sec L}
    (hb : ∀ s : LB.Sec L, ∃! a : K, ∀ i, s.f i = constFn p _ a * b.f i) : ∃ i, ∃ y ∈ L.U i, gs (𝟙 X) y _ (b.f i) ≠ 0 := by
  by_contra hne
  push_neg at hne
  have hb0 : ∀ i, b.f i = 0 := fun i => fn_ext fun y hy => by
    rw [hne i y hy]
    unfold gs
    split_ifs
    · rw [map_zero, map_zero]
    · rfl
  obtain ⟨a, -, hu⟩ := hb b
  have h0 := hu 0 fun i => by rw [hb0 i, mul_zero]
  have h1 := hu 1 fun i => by rw [hb0 i, mul_zero]
  exact zero_ne_one (h0.trans h1.symm)

end H0

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : Unif (maximalIdeal R) D A G)

theorem exists_ne_zero (hT : SecTwistSt) : ∃ σ : H0 U.LG.L 1, ¬ ∀ j, σ.f j = 0 := by
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT A
  obtain ⟨i, y, hy, hne⟩ := ne_zero_of_gen hb
  obtain ⟨w, hw⟩ := LBIso.symm U.ext
  have hL := U.LG.isLB
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff w).1 hw) A.isLB (pull_isLB hL _) b
  obtain ⟨s, hs⟩ := exists_sec hL (φ := fun _ : PUnit => pullback.fst G.hom (jK R)) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => ((1 : ℕ) : ℤ)) (fun V _ h => by simp) s'
  obtain ⟨F, ⟨r, hr, σ, f, h₁, -, -⟩, -⟩ := (U.expand 1 le_rfl).1 s
  refine ⟨σ, fun h0 => hne ?_⟩
  let ρ := U.gen.inv.left
  have e : ρ ≫ U.gen.hom.left = 𝟙 _ := congrArg (fun q => q.left) U.gen.inv_hom_id
  choose J hJ using fun χ : A.A.left ⟶ G.left => exists_chart hL (χ y)
  have m := Good.mem hJ (fun _ : Fin 1 => pullback.fst G.hom (jK R)) ρ
  have m' := Good.mem hJ (fun _ : PUnit => pullback.fst G.hom (jK R)) ρ
  have k := hs' _ ρ y i _ ((congrArg (fun q => q y ∈ A.L.U i) e).mpr hy) m'
  rw [e] at k
  have k₂ := congrArg (gs ρ y _) (h₁ (fun _ => J (ρ ≫ pullback.fst G.hom (jK R))) (fun _ => J (ρ ≫ pullback.fst G.hom (jK R)))
    (by rintro (a | a) (c | c) _ <;> rfl))
  have mm : ρ y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => J (ρ ≫ pullback.fst G.hom (jK R))) ⊓
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 _) (fun _ => J (ρ ≫ pullback.fst G.hom (jK R))) := ⟨m, m⟩
  have k₀ := (gs_zero ρ y _ mm).symm.trans ((congrArg (gs ρ y _) ((map_zero _).symm.trans (congrArg _ ((map_zero _).symm.trans
    (congrArg _ (h0 _).symm))))).trans k₂)
  have k₃ := (k₀.trans (gs_mul ρ y _ mm _ _)).trans (congrArg₂ (· * ·) (gs_constFn (pullback.snd G.hom (jK R) ≫ jK R) _ ρ y mm r)
    ((gs_res ρ y inf_le_left mm _).trans (hs _ ρ y J hJ)))
  have hu : IsUnit (cst (ρ ≫ pullback.snd G.hom (jK R) ≫ jK R) y r) := by
    rw [← Category.assoc, (cst_comp _ (algebraMap R (FractionRing R)) y r : cst (_ ≫ jK R) y r = _)]
    exact IsUnit.of_mul_eq_one _ ((cst_mul _ y _ (algebraMap R (FractionRing R) r)⁻¹).symm.trans (by
      rw [mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hr), cst_one]))
  exact k.trans ((congrArg _ ((hu.mul_right_eq_zero).1 k₃.symm)).trans (mul_zero _))

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
