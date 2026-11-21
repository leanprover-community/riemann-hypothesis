import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeRatio

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def gam (A : Type) [CommRing A] : Γ(Sp A, ⊤) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem gam_toΓ (A : Type) [CommRing A] (a : A) : gam A (toΓ A a) = a := by
  simp [gam, toΓ]

theorem gam_pull {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Γ(Sp A, ⊤)) :
    gam B (((spMap f).app ⊤).hom x) = f (gam A x) := by
  have h := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [gam, spMap]
  exact h

theorem gam_pullUnit {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Γ(Sp A, ⊤)ˣ) :
    gam B (pullUnit (spMap f) u : Γ(Sp B, ⊤)) = f (gam A u) := by
  simp only [pullUnit, pullU, Units.coe_map, MonoidHom.coe_coe]
  exact gam_pull f (u : Γ(Sp A, ⊤))

theorem scaled_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {Y : Scheme.{0}} {K : Type} [Fintype K]
    (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} (h : IsScaled u t t') (k : ℕ) :
    IsScaled (u ^ k) (genPow φ ε t k) (genPow φ ε t' k) := by
  unfold IsScaled at h ⊢
  intro j
  show t'.s j ^ k = _ * t.s j ^ k
  rw [h j, mul_pow, map_pow]
  rfl

theorem value_scaled {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (a : ℤ)
    {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v v' : Γ(T.left, ⊤)) (U : Γ(T.left, ⊤)ˣ) (h : IsValueAt A L a s z τ v) (h' : IsValueAt A L a s z τ' v')
    (hs : IsScaled U τ τ') : v = (U : Γ(T.left, ⊤)) * v' := by
  unfold IsValueAt at h h'
  unfold IsScaled at hs
  have key : ∀ j, (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom v =
      (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom ((U : Γ(T.left, ⊤)) * v') := by
    intro j
    have e := (h j).symm.trans (h' j)
    have e2 := congrArg Units.val (hs j)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e2
    simp only [e2] at e
    rw [map_mul]
    refine (Units.mul_left_inj (τ.s j)).mp ?_
    calc _ = _ := e
      _ = _ := mul_left_comm _ _ _
      _ = _ := (mul_assoc _ _ _).symm
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j, (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := by
    intro x _
    have hx : z.left.base x ∈ (⊤ : A.left.Opens) := trivial
    rw [← hL.cover] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ => i, ?_⟩
    show x ∈ L.wchart (fun _ => z.left) (fun _ => i)
    unfold LB.wchart
    exact Set.mem_iInter.mpr fun _ => hi
  exact T.left.sheaf.eq_of_locally_eq' _ ⊤ (fun j => homOfLE le_top) hcov v ((U : Γ(T.left, ⊤)) * v') key

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem cc_smul_q {S σ : Type} [CommRing S] {q : MvPowerSeries σ S} (hq : MvPowerSeries.constantCoeff q = 0)
    (r : S) : MvPowerSeries.constantCoeff (r • q) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hq, mul_zero]

theorem exp_pow_eq {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) : ∀ k : ℕ,
    PowerSeries.subst q (PowerSeries.exp S) ^ k = PowerSeries.subst ((k : S) • q) (PowerSeries.exp S)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_smul, exp_zero]
  | k + 1 => by
    rw [pow_succ, exp_pow_eq q hq k, ← exp_add (ha := cc_smul_q hq (k : S)) (hb := hq), Nat.cast_succ, add_smul,
      one_smul]

theorem exp_pow_mul_exp_neg {S σ : Type} [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S)
    (hq : MvPowerSeries.constantCoeff q = 0) (k : ℕ) :
    PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1 := by
  have hneg : MvPowerSeries.constantCoeff (-((k : S) • q)) = 0 := by
    rw [map_neg, cc_smul_q hq, neg_zero]
  rw [exp_pow_eq q hq k, ← exp_add (cc_smul_q hq _) hneg, add_neg_cancel, exp_zero]

end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeR
end
end

section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def ExpPowSt : Prop :=
  ∀ (S σ : Type) [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S), MvPowerSeries.constantCoeff q = 0 →
    ∀ k : ℕ, PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1

theorem gaugeUniq_of' (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring

end GaugeR

theorem gaugeUniq_of (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k

theorem gaugeUniq_of_global (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
