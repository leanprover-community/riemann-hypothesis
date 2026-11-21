import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericallySmoothModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometricStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comb_pow_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L : HermLB p) (m : ℕ), (ArInt.comb (fun _ : Unit => L) (fun _ => (m : ℤ))).Isometric (L.pow m) := by
  first | exact @GlobalTheory.ArInt.isometric_comb_unit_pow | exact GlobalTheory.ArInt.isometric_comb_unit_pow | (intros; apply GlobalTheory.ArInt.isometric_comb_unit_pow <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_weight_linear_comb : ∀ (k k' : Type) [CommRing k] [CommRing k'] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k') (σ : k →+* ℂ) (σ' : k' →+* ℂ) (D : ℕ) (j : Y ⟶ X) (Φ : CxPts q σ' ≃ₜ CxPts p σ) (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j) [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')], Nonempty (AnRead p σ D) → Nonempty (AnRead q σ' D) → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → (φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)).IsCInf ∧ (φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)).chernInt D Set.univ (fun _ => 1) = φ.chernInt D Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_transfer | exact GlobalTheory.chernInt_transfer | (intros; apply GlobalTheory.chernInt_transfer <;> assumption)
end

section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TwistTop

theorem exists_homeomorph : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : Model Y) (σ : F →+* ℂ), ∃ Φ : CxPts Y.str σ ≃ₜ CxPts M.p (σ.comp (algebraMap (𝓞 F) F)), ∀ z, (Φ z).1 = z.1 ≫ M.j := fun F _ _ Y M σ => by
  have e : spMap σ ≫ spMap (algebraMap (𝓞 F) F) = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← Spec.map_comp]; rfl
  have h₁ (z : CxPts Y.str σ) : (z.1 ≫ M.j) ≫ M.p = spMap (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, z.2, e]
  have h₂ : Continuous fun y : CxPts M.p (σ.comp (algebraMap (𝓞 F) F)) =>
      M.pb.lift y.1 (spMap σ) (y.2.trans e.symm) := by
    rw [(Points.isEmbedding_of_isPullback M.pb).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap σ))).congr fun y => ?_
    exact (Prod.ext (M.pb.lift_fst _ _ _) (M.pb.lift_snd _ _ _)).symm
  exact ⟨{ toFun := fun z => ⟨z.1 ≫ M.j, h₁ z⟩
           invFun := fun y => ⟨M.pb.lift y.1 (spMap σ) (y.2.trans e.symm), M.pb.lift_snd _ _ _⟩
           left_inv := fun z => Subtype.ext (M.pb.hom_ext (M.pb.lift_fst _ _ _)
             ((M.pb.lift_snd _ _ _).trans z.2.symm))
           right_inv := fun y => Subtype.ext (M.pb.lift_fst _ _ _)
           continuous_toFun := ((Points.continuous_comp M.j).comp continuous_subtype_val).subtype_mk h₁
           continuous_invFun := h₂.subtype_mk fun y => M.pb.lift_snd _ _ _ }, fun _ => rfl⟩

theorem bijective_comp_algebraMap (F : Type) [Field F] [NumberField F] :
    Function.Bijective fun σ : F →+* ℂ => σ.comp (algebraMap (𝓞 F) F) := by
  refine ⟨fun σ τ h => IsLocalization.ringHom_ext (S := F) (nonZeroDivisors (𝓞 F)) (j := σ) (k := τ) h, fun τ => ?_⟩
  have hi : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
    have : (n : ℂ) = 0 := (map_intCast τ n).symm.trans hn
    exact Int.cast_eq_zero.1 this
  exact ⟨IsFractionRing.lift (K := F) hi, RingHom.ext fun a => IsFractionRing.lift_algebraMap (K := F) hi a⟩

theorem chernInt_model (hd : GlobalTheory.Published.ChernDegree) {F : Type} [Field F] [NumberField F] {Y : Var F} (M : Model Y)
    (L : HermLB M.p) {Δ : Y.Dv} {r : (L.B.pull M.j).ι → Y.Fnˣ} (h : Presents Δ (L.B.pull M.j) r) (σ : F →+* ℂ) :
    (L.φ (σ.comp (algebraMap (𝓞 F) F))).chernInt Y.dim Set.univ (fun _ => 1) = (Y.inter (fun _ => Δ) : ℝ) := by
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph F Y M σ
  have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap (𝓞 F) F)) M.ar.isProjOver
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.analytic_weight_linear_comb _ _ _ _ M.p Y.str _ σ Y.dim M.j Φ hΦ (GlobalTheory.T.generically_smooth_model F Y M _) inferInstance _ _ (L.cInf _)
  exact h₂.symm.trans (hd F Y σ Δ _ r h _ h₁).2

theorem sum_emb {F : Type} [Field F] [NumberField F] (c : InfinitePlace F → ℝ) :
    ∑ σ : F →+* ℂ, c (InfinitePlace.mk σ) = ∑ v : InfinitePlace F, (v.mult : ℝ) * c v := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl fun σ hσ => congrArg c (Finset.mem_filter.1 hσ).2, Finset.sum_const,
    InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem isArTop_twist : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (t : ℝ) (ci : InfinitePlace F → ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support cf).Finite → A.IsArTop t → (A.twist ci cf).IsArTop (t + ((Y.dim : ℝ) + 1) * A.deg * ((∑ v : InfinitePlace F, (v.mult : ℝ) * ci v) + ∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ)) := by
  intro hc hd F _ _ C Y A t ci cf hcf ⟨M, L, k, cf₀, a, ⟨hf, r, hr, hi, hv⟩, ha, ht⟩
  have := M.ar.isIntegral
  let E := Equiv.ofBijective _ (bijective_comp_algebraMap F)
  have hE (σ : F →+* ℂ) : E.symm (σ.comp (algebraMap (𝓞 F) F)) = σ := E.symm_apply_apply σ
  let s (τ : 𝓞 F →+* ℂ) : ℝ := (k : ℕ) * (A.n : ℕ) * ci (InfinitePlace.mk (E.symm τ))
  have hs (τ : 𝓞 F →+* ℂ) : s ((starRingEnd ℂ).comp τ) = s τ := by
    obtain ⟨σ, rfl⟩ := E.surjective τ
    have e : (starRingEnd ℂ).comp (E σ) = E (ComplexEmbedding.conjugate σ) := rfl
    simp only [s, e, Equiv.symm_apply_apply, InfinitePlace.mk_conjugate_eq]
  refine ⟨M, L.shift s hs, k, cf₀ + cf, _, ⟨(hf.union hcf).subset (Function.support_add _ _), r, hr,
    fun σ y y' i f h₁ h₂ h₃ => ?_, fun v e y yt i h₁ h₂ => ?_⟩, isSelfInter_shift hc.1 hc.2.1 _ _ _ _ M.ar L a s hs ha, ?_⟩
  · have e := hi σ y y' i f h₁ h₂ h₃
    change Real.exp (-(2 * (k : ℕ) * (A.n : ℕ) * (A.ci (InfinitePlace.mk σ) + ci (InfinitePlace.mk σ)))) *
      C.pn Y σ _ (C.mPow Y σ A.D k (A.m σ)) (C.cx Y σ f) y =
      ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-((L.φ _).φ (i PUnit.unit) y' + 2 * s _))
    rw [neg_add, Real.exp_add, ← mul_assoc, ← e, mul_add, neg_add, Real.exp_add, mul_right_comm]
    simp only [s, hE, mul_assoc]
  · have e := hv v e y yt i h₁ h₂
    change ((k : ℕ) : ℝ) * (A.lg v _ y - (A.n : ℕ) * cf v) = Real.log (Ext.w _ (valAt y.1
      (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) * r i : Y.Fnˣ) : Y.Fn))) - (k : ℕ) * (A.n : ℕ) * (cf₀ v + cf v)
    linear_combination e
  · have e₁ : ∑ᶠ τ, s τ * (L.φ τ).chernInt Y.dim Set.univ (fun _ => 1) =
        (k : ℕ) * (A.n : ℕ) * (((k : ℕ) : ℝ) ^ Y.dim * (Y.inter (fun _ => A.D) : ℝ)) *
          ∑ v : InfinitePlace F, (v.mult : ℝ) * ci v := by
      rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype, ← sum_emb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      have e := chernInt_model hd.2 M L hr σ
      rw [Var.inter_const_nsmul] at e
      push_cast at e
      rw [show (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) = _ from e]
      simp only [s, Equiv.symm_apply_apply]
      ring
    have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
    have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
    have e₂ : ∑ᶠ v, (cf₀ + cf) v = ∑ᶠ v, cf₀ v + ∑ᶠ v, cf v := finsum_add_distrib hf hcf
    rw [e₁, e₂, ht, deg_twist, ← add_div]
    congr 1
    simp only [Adl.deg, Adl.twist]
    field_simp
    ring

end GlobalTheory.TwistTop
end
end

section
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.ModelShift

theorem isSelfInter_shift_model : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r → ∀ (t : (𝓞 F →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (a : ℝ), (haveI := M.ar.isIntegral; L.IsSelfInter a) → (haveI := M.ar.isIntegral; (L.shift t ht).IsSelfInter (a + ((Y.dim : ℝ) + 1) * (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)))) := by
  intro hc hd F _ _ Y M L Δ r hr t ht a ha
  have := M.ar.isIntegral
  let E := Equiv.ofBijective _ (TwistTop.bijective_comp_algebraMap F)
  have key (σ : F →+* ℂ) : (L.φ (σ.comp (algebraMap (𝓞 F) F))).chernInt Y.dim Set.univ (fun _ => 1) =
      (Y.inter (fun _ => Δ) : ℝ) := by
    obtain ⟨Φ, hΦ⟩ := TwistTop.exists_homeomorph F Y M σ
    have := CxPts.secondCountableTopology_of_isProjOver (σ.comp (algebraMap (𝓞 F) F)) M.ar.isProjOver
    obtain ⟨h₁, h₂⟩ := GlobalTheory.chernInt_transfer _ _ _ _ M.p Y.str _ σ Y.dim M.j Φ hΦ
      (GlobalTheory.ModelCharts.genSmooth_model F Y M _) inferInstance _ _ (L.cInf _)
    exact h₂.symm.trans (hd.2 F Y σ Δ _ r hr _ h₁).2
  have e₁ : ∑ᶠ τ, t τ * (L.φ τ).chernInt Y.dim Set.univ (fun _ => 1) =
      (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)) := by
    rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) = _ from key σ, mul_comm]
    rfl
  have h := TwistTop.isSelfInter_shift hc.1 hc.2.1 _ _ _ _ M.ar L a t ht ha
  rw [e₁, ← mul_assoc] at h
  exact h

end GlobalTheory.ModelShift
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_intersection_shift : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r → ∀ (t : (𝓞 F →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (a : ℝ), (haveI := M.ar.isIntegral; L.IsSelfInter a) → (haveI := M.ar.isIntegral; (L.shift t ht).IsSelfInter (a + ((Y.dim : ℝ) + 1) * (Y.inter (fun _ => Δ) : ℝ) * ∑ σ : F →+* ℂ, t (σ.comp (algebraMap (𝓞 F) F)))) := by
  atlas_forward_decl GlobalTheory.ModelShift.isSelfInter_shift_model
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_pullback : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p), N.j ≫ π = M.j → ∀ (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced N (L.pull π hπ) k cf := by
  first | exact @GlobalTheory.TrueGeo.InducedPull.induced_pull | exact GlobalTheory.TrueGeo.InducedPull.induced_pull | (intros; apply GlobalTheory.TrueGeo.InducedPull.induced_pull <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k m : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M (L.pow m) (k * m) cf := by
  first | exact @GlobalTheory.TrueGeo.InducedPow.induced_pow | exact GlobalTheory.TrueGeo.InducedPow.induced_pow | (intros; apply GlobalTheory.TrueGeo.InducedPow.induced_pow <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_shift_element : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (b : 𝓞 F), b ≠ 0 → ∀ ht : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖, A.Induced M L k cf → A.Induced M (L.shift (fun σ => Real.log ‖σ b‖) ht) k (fun v => cf v + Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) := by
  first | exact @GlobalTheory.TrueGeo.IndScale.induced_shift | exact GlobalTheory.TrueGeo.IndScale.induced_shift | (intros; apply GlobalTheory.TrueGeo.IndScale.induced_shift <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_difference_log : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L L' : HermLB M.p) (k : ℕ+) (cf cf' : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → A.Induced M L' k cf' → ∀ v : HeightOneSpectrum (𝓞 F), ∃ (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 ∧ ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v) = Real.log (e.w α) := by
  first | exact @GlobalTheory.TrueGeo.ValGroup.main | exact GlobalTheory.TrueGeo.ValGroup.main | (intros; apply GlobalTheory.TrueGeo.ValGroup.main <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_absolute_value_rational : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 → ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * Real.log (e.w α) = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.ExtValueGroup.log_w_rat | exact GlobalTheory.ExtValueGroup.log_w_rat | (intros; apply GlobalTheory.ExtValueGroup.log_w_rat <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_element_height_difference : ∀ (F : Type) [Field F] [NumberField F] (c : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support c).Finite → (∀ v, ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * c v = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ)) → ∃ (h : ℕ+) (b b' : 𝓞 F), b ≠ 0 ∧ b' ≠ 0 ∧ ∀ v, ((h : ℕ) : ℝ) * c v = Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) - Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b')) := by
  first | exact @GlobalTheory.exists_mul_eq_log_adicAbv_sub | exact GlobalTheory.exists_mul_eq_log_adicAbv_sub | (intros; apply GlobalTheory.exists_mul_eq_log_adicAbv_sub <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratIsom_of_induced_hermitian_bundles : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (N : TrueGeo.Model Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X → ∀ (L L' : HermLB N.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced N L k cf → A.Induced N L' k cf → (haveI := N.ar.isIntegral; RatIsom L L') := by
  first | exact @GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced | exact GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced | (intros; apply GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ArUniq

theorem isSelfInter_pow (hC : GlobalTheory.Published.ArCalc) {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (hX : IsArithVar p D) {L : HermLB p} {a : ℝ} (ha : L.IsSelfInter a) (m : ℕ) :
    (L.pow m).IsSelfInter ((m : ℝ) ^ (D + 1) * a) := by
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, e⟩ := hΦ.1 fun _ => (m : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.T.comb_pow_isometric k X p L m) hH, e.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

def Reads (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ) (t : ℝ) :
    Prop :=
  A.Induced M L k cf ∧ ∃ a : ℝ, (haveI := M.ar.isIntegral; L.IsSelfInter a) ∧
    t = (a / (((k : ℕ) : ℝ) * (A.n : ℕ)) ^ (Y.dim + 1) + ((Y.dim : ℝ) + 1) * A.deg * ∑ᶠ v, cf v) /
      (Module.finrank ℚ F : ℝ)

variable {M : TrueGeo.Model Y} {L : HermLB M.p} {k : ℕ+} {cf : HeightOneSpectrum (𝓞 F) → ℝ} {t : ℝ}

theorem Reads.pull (hB : GlobalTheory.Published.ArBirational) (h : Reads A M L k cf t) (N : TrueGeo.Model Y) (π : N.X ⟶ M.X)
    (hπ : π ≫ M.p = N.p) (hj : N.j ≫ π = M.j) (hU : ∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) :
    Reads A N (L.pull π hπ) k cf t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  obtain ⟨U, hU, hU'⟩ := hU
  have := M.ar.isIntegral
  have := N.ar.isIntegral
  exact ⟨GlobalTheory.T.induced_metric_pullback F C Y A M N π hπ hj L k cf hI, a,
    hB _ M.X N.X M.p N.p Y.dim M.ar N.ar (GlobalTheory.T.generically_smooth_model F Y M) (GlobalTheory.T.generically_smooth_model F Y N) π hπ U hU hU' L a ha, ht⟩

theorem Reads.pow (hE : GlobalTheory.Published.ArCalc) (h : Reads A M L k cf t) (m : ℕ+) :
    Reads A M (L.pow m) (k * m) cf t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  have := M.ar.isIntegral
  refine ⟨GlobalTheory.T.induced_metric_pow F C Y A M L k m cf hI, _, isSelfInter_pow hE M.ar ha m, ?_⟩
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [ht, PNat.mul_coe, Nat.cast_mul]
  congr 2
  rw [mul_right_comm, mul_pow _ ((m : ℕ) : ℝ)]
  field_simp

theorem Reads.scale (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree) (h : Reads A M L k cf t) {b : 𝓞 F} (hb : b ≠ 0) :
    ∃ L' : HermLB M.p, Reads A M L' k (fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / (((k : ℕ) : ℝ) * (A.n : ℕ))) t := by
  obtain ⟨hI, a, ha, ht⟩ := h
  have hc : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖ := fun σ => by simp
  obtain ⟨hf, r, hr, -⟩ := id hI
  refine ⟨_, GlobalTheory.T.induced_metric_shift_element F C Y A M L k cf b hb hc hI, _,
    GlobalTheory.T.self_intersection_shift hC hD F Y M L _ r hr (fun σ => Real.log ‖σ b‖) hc a ha, ?_⟩
  obtain ⟨h₁, h₂⟩ := GlobalTheory.sum_log_embedding_add_finsum_log_adicAbv_eq_zero F (algebraMap (𝓞 F) F b) (by simpa using hb)
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [finsum_add_distrib hf (h₁.subset fun v hv h0 => hv (by simp only [h0, zero_div]))]
  simp only [div_eq_mul_inv (Real.log _)]
  rw [← finsum_mul' _ _ h₁, eq_neg_of_add_eq_zero_right h₂, ht, Y.inter_const_nsmul, Adl.deg]
  simp only [RingHom.comp_apply]
  congr 1
  push_cast
  field_simp
  ring

theorem Reads.eq (hC : GlobalTheory.Published.ArCalc) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {L' : HermLB M.p} {t' : ℝ}
    (h : Reads A M L k cf t) (h' : Reads A M L' k cf t') : t = t' := by
  obtain ⟨hI, a, ⟨H, hH, rfl⟩, rfl⟩ := h
  obtain ⟨hI', a', ha', rfl⟩ := h'
  have := M.ar.isIntegral
  have e := HermLB.IsSelfInter.unique M.ar ⟨H, (hC.arIso _ M.X M.p Y.dim M.ar).1 L L' H
    (GlobalTheory.T.rational_isometry_isometric _ M.X M.p L L' (GlobalTheory.T.ratIsom_of_induced_hermitian_bundles F C Y A M hN L L' k cf hI hI')) hH, rfl⟩ ha'
  rw [e]

theorem Reads.eq' (hC : GlobalTheory.Published.ArCalc) (hD : GlobalTheory.Published.ArDegree)
    (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) {L' : HermLB M.p} {t' : ℝ}
    {cf' : HeightOneSpectrum (𝓞 F) → ℝ} (h : Reads A M L k cf t) (h' : Reads A M L' k cf' t') : t = t' := by
  obtain ⟨m, b, b', hb, hb', e⟩ := GlobalTheory.T.exists_element_height_difference F (fun v => ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v))
    ((h.1.1.union h'.1.1).subset fun v hv => by
      by_contra h0
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h0
      simp [h0.1, h0.2] at hv) fun v => by
    obtain ⟨e, α, hα, h₁⟩ := GlobalTheory.T.induced_metric_difference_log F C Y A M L L' k cf cf' h.1 h'.1 v
    rw [h₁]
    exact GlobalTheory.T.log_absolute_value_rational F v e α hα
  obtain ⟨L₁, h₁⟩ := (h.pow hC m).scale hC hD hb
  obtain ⟨L₂, h₂⟩ := (h'.pow hC m).scale hC hD hb'
  refine h₁.eq hC hN (L' := L₂) ?_
  convert h₂ using 2 with v
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  rw [sub_eq_iff_eq_add.1 (e v).symm, PNat.mul_coe, Nat.cast_mul]
  field_simp
  ring

theorem isArTop_unique : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F)
    (Y : Var F) (A : Adl C Y) (t t' : ℝ), A.IsArTop t → A.IsArTop t' → t = t' := by
  rintro hC hD F _ _ C Y A t t' ⟨M, L, k, cf, a, hI, ha, ht⟩ ⟨M', L', k', cf', a', hI', ha', ht'⟩
  obtain ⟨N, π, π', hN, hπ, hπ', hj, hj', hU, hU'⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M'
  have h₁ := (Reads.pull hD.1 ⟨hI, a, ha, ht⟩ N π hπ hj hU).pow hC k'
  have h₂ := (Reads.pull hD.1 ⟨hI', a', ha', ht'⟩ N π' hπ' hj' hU').pow hC k
  rw [mul_comm k' k] at h₂
  exact h₁.eq' hC hD hN h₂

end GlobalTheory.TrueGeo.ArUniq
end
end
