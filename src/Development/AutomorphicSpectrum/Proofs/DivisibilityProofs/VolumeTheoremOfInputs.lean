import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoSeriesThreeStep
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PropFTopHolds
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AgreementPositive
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Antisymmetry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Coefficients
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagHeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarizationStatement
import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerBounds
import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFifthCondition
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditions
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerM1Nef
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerOriginVectorBundle
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2
import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelRealTowerSmooth
import Development.WeilBound.CoreStatements.FlagImmersions.GlobalModelTowerFinalCondition
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreement
import Development.WeilBound.CoreStatements.VolumeEquality.VolEqOfIsFullIntersectionSystem
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.RefLinked
import Development.WeilBound.CoreStatements.FlagImmersions.RealTowerMeanSlopeCondition
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerI1
import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetry
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerNefGeneral
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagHodgeStatement
import Development.WeilBound.CoreStatements.FlagImmersions.RootModelNefFibresBase
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasBaseDegreeSettingStrict
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotal
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilInputsCombined
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseSettingOfGoodTower

section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

namespace DeltaTermLin

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_add (F G : RP Ψ N) : degFl (F + G) = degFl F + degFl G := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]

theorem degFl_zero : degFl (0 : RP Ψ N) = 0 := by
  simp [degFl]

theorem degFl_C_mul (a : ℝ) (F : RP Ψ N) : degFl (C a * F) = a * degFl F := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem degFl_sum {ι : Type} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degFl_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, degFl_add, ih]

end DeltaTermLin

theorem log_mul_degFl_bracket_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ (φ : Equiv.Perm (Ψ ⊕ Ψ)) (τ : Ψ) (Q : RP Ψ N), Real.log p * degFl (bracket j φ p k τ * Q) = deltaTerm j p τ (fun n => (φ ^ (n + 1)) (Sum.inl τ)) k Q := by
  intro Ψ _ _ N j p k hp hk φ τ Q
  have hlie : ∀ σ : Ψ ⊕ Ψ, liePs (N := N) j (k - 1) σ = pLie j (k - 1) σ := by
    rintro (s | s) <;> rfl
  have hco := co_series_three_step.1 (Ψ ⊕ Ψ) φ p k hp hk
    (fun σ => degFl (pLie (N := N) j (k - 1) σ * Q)) (Sum.inl τ)
  have hb : degFl (bracket j φ p k τ * Q) =
      (k : ℝ) * ∑ σ, co φ p k (Sum.inl τ) σ * degFl (pLie (N := N) j (k - 1) σ * Q) := by
    unfold bracket
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, Finset.sum_mul, DeltaTermLin.degFl_sum]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [mul_assoc, DeltaTermLin.degFl_C_mul, hlie]
  rw [hb, hco]
  simp only [deltaTerm, pLie]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

section
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

open Filter Topology

theorem arFun_tendsto_PP {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : RootModel Ψ N) (II : IntersectionSystem)
    (h : M.Converges II) (F : RPA Ψ N) :
    Tendsto (fun t => M.arFun II t F) (𝓝[>] 0) (𝓝 (M.PP II F)) := by
  classical
  simp only [GlobalTheory.CompanionTheory.Ar.Top.RootModel.arFun, GlobalTheory.CompanionTheory.Ar.Top.RootModel.PP, Module.Basis.constr_apply, Finsupp.sum]
  refine tendsto_finsetSum _ (fun m _ => ?_)
  obtain ⟨L, hL⟩ := h m
  exact (tendsto_nhds_limUnder ⟨L, hL⟩).const_smul _

theorem PP_eq_add_of_arFun_eq_add :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II →
      M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) →
      M.PP II F = M'.PP II F + c := by
  intro Ψ _ N M M' II hM hM' F c hF
  have h1 := arFun_tendsto_PP M II hM F
  have h2 := (arFun_tendsto_PP M' II hM' F).add_const c
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hF t ht).symm

end GlobalTheory.CompanionTheory.Ar.Num
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_height_constant_shift : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II → M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) → M.PP II F = M'.PP II F + c := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add
end

section
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem power_sum_term_linked_tower : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → T.Proportional → ∀ φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ), LinkedTower T II φ → T.Prop6 II fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  intro Ψ _ _ N T II hII hprop φ hL
  intro B₀ B hB₀ hB c τ k hk1 hkN Q hQ
  obtain ⟨M, R, S, hS, hMc, hRc, hMPP, hRPP, hgeo, hch, hloc⟩ := hL B₀ B hB₀ hB c
  have hstep := GlobalTheory.T.limit_height_constant_shift Ψ N M R.model II hMc hRc (toA (pk τ k * Q))
    (∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket T.j (φ p) p k τ * Q)))
    (fun t ht => GlobalTheory.T.power_sum_height_change_model Ψ N M R II hII S T.j φ hch hloc t ht τ k hk1 hkN Q hQ)
  rw [hMPP, hRPP] at hstep
  rw [hstep]
  congr 1
  have hSeq : S.map ⟨(fun p : Nat.Primes => (p : ℕ)), Nat.Primes.coe_nat_injective⟩ =
      (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Ioc, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have h := (hS p).1 hp
      exact ⟨⟨h.1, h.2.1⟩, p.2, h.2.2⟩
    · rintro ⟨⟨h1, h2⟩, hpr, hbad⟩
      exact ⟨⟨n, hpr⟩, (hS _).2 ⟨h1, h2, hbad⟩, rfl⟩
  rw [← hSeq, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  change _ = T.vol c * deltaTerm T.j (p : ℕ) τ (fun n => (φ (p : ℕ) ^ (n + 1)) (Sum.inl τ)) k Q
  rw [hgeo, hprop.2.1, ← log_mul_degFl_bracket_mul Ψ N T.j p k p.2.two_le hk1 (φ p) τ Q]
  ring

end GlobalTheory.CompanionTheory.Ar.Num
end

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_tower_power_sum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → T.Proportional → ∀ φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ), LinkedTower T II φ → T.Prop6 II fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem effDiff_of_goodOrigin : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu :=
  @RootFieldNumerics.global_model_tower_bounds

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_conditions : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ B a, (T.M B a).EffDiff T.nu := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.effDiff_of_goodOrigin
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem i5_and_i6_of_isGlobal_of_goodOrigin : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II :=
  RootFieldNumerics.global_model_tower_fifth_condition

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_I5 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I5 II ∧ T.I6 II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.i5_and_i6_of_isGlobal_of_goodOrigin
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem m2_of_good_tower : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o II hglob _ hp hq
  obtain ⟨Yl, hg, hloc, -, -, hdom⟩ := hglob
  intro B a p hpr hnS mu hmu hnef
  have hpbad : p ∉ T.bad := fun hb =>
    hnS (show Nat.Prime p ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hpr, Or.inr hb⟩)
  have h2 : 2 < p := lt_of_le_of_ne hpr.two_le (fun h => hpbad (by rw [← h]; exact T.two_mem))
  have hdisc : ¬ ((p : ℤ) ∣ NumberField.discr E) := fun hd =>
    hpbad ((o.toTowerOrigin.bad_iff p).2 ⟨hpr, dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _⟩)
  have hpS : p ∉ o.toTowerOrigin.S B := fun h => hnS ((o.toTowerOrigin.S_iff B p).1 h)
  rw [o.toTowerOrigin.j_eq] at hnef
  exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl
    (fun p W hp hW i => ⟨((hloc p W hp hW).2 i).1, ((hloc p W hp hW).2 i).2.1⟩)
    l c hg Y hdom hp hq (o.toTowerOrigin.S B) (T.M B a) (o.toTowerOrigin.Or B a).𝔐
    (o.toTowerOrigin.Or B a).Fl (o.toTowerOrigin.Or B a).e (o.toTowerOrigin.Or B a).lines
    p hpr h2 hpS hdisc mu hmu hnef

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_M2 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.m2_of_good_tower
end

section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_origin_vector_bundle : CmpPair → TwistAut → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : TowerOrigin Y T), IsGalois ℚ E → (∀ B a, (o.Or B a).𝔐.OmVB) → (∀ a, (∀ x : (o.Sys a).X, ∃ (U : Set (o.Sys a).X) (lam : (o.Sys a).X → Fin ((o.Fx a).m + 1) → ℂ), IsOpen U ∧ x ∈ U ∧ (∀ i, (o.Sys a).A.HoloOn U fun y => lam y i) ∧ (∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • (o.Fx a).pt y) ∧ ∀ p, lam x p ≠ 0 → ∀ j, x ∈ ((o.Sys a).A.chart j).source → (fderiv ℂ (fun z i => lam (((o.Sys a).A.chart j).symm z) i / lam (((o.Sys a).A.chart j).symm z) p) ((o.Sys a).A.chart j x)).ker = ⊥)) → (∀ B a a', ∀ p ∈ o.S B, (o.Or B a').𝔐.R p = (o.Or B a).𝔐.R p) → T.Conv II → T.PropA II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TowerPropA.propA_of_origin | exact GlobalTheory.CompanionTheory.Ar.TowerPropA.propA_of_origin | (intros; apply GlobalTheory.CompanionTheory.Ar.TowerPropA.propA_of_origin <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem propA_of_goodOrigin : PB.AgreementPos → TwistAut → Cmp.CmpPair → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.PropA II := by
  intro hAg hTw hCmp hG E _ _ _ _ H D Xo l c Y _ T o II _ hX hII _ _
  obtain ⟨_, _, _, _, _, _, _, _, _, hIn, _⟩ := hG
  have hConv : T.Conv II := (GlobalTheory.T.real_tower_conv_I2 hAg hIn II hII (CMType H) (D.p + D.q) T (realOf o.toTowerOrigin)).1
  refine GlobalTheory.T.tower_origin_vector_bundle hCmp hTw II hII E H D l (Xo l) c Y T o.toTowerOrigin inferInstance o.omVB hX.1 ?_ hConv
  intro B a a' p hp
  rw [hX.2 B a p hp, hX.2 B a' p hp]

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_propA_of_global_extra : PB.AgreementPos → TwistAut → Cmp.CmpPair → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.PropA II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.propA_of_goodOrigin
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_real_I6 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).RefLinked II := by
  first | exact @RootFieldNumerics.global_model_real_tower_smooth | exact RootFieldNumerics.global_model_real_tower_smooth
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_I6 : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).RefLinked II := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.good_tower_real_I6
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_real_extra : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  first | exact @RootFieldNumerics.global_model_tower_final_condition | exact RootFieldNumerics.global_model_tower_final_condition
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_real_extra : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.good_tower_real_extra
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.good_tower_intersection_extra : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  first | exact @SheetDecomposition.volEq_of_isFullIntersectionSystem | exact SheetDecomposition.volEq_of_isFullIntersectionSystem
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_intersection_extra : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → T.VolEq := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Relay.good_tower_intersection_extra
end

section
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem tower_A1_of_real_tower : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T),
      R.Smooth → R.Flat → R.Pos → T.A1 :=
  @RootFieldNumerics.real_tower_mean_slope_condition

end GlobalTheory.CompanionTheory.Ar.Top
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_tower_A1 : PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (R : RealTower T), R.Smooth → R.Flat → R.Pos → T.A1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.tower_A1_of_real_tower
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem full_intersection_tower_I8_relation : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  @SquareStatements.good_tower_antisymmetry

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_intersection_tower_I8_identity : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.full_intersection_tower_I8_relation
end

section
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem rootModel_nefFib_zero_one_of_nonneg :
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 :=
  @RootFieldNumerics.root_model_nef_fibres_base

end GlobalTheory.CompanionTheory.Ar.Top
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_nef_fibres : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N), (∀ k, 0 ≤ M.A.a k) → M.NefFib 0 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.rootModel_nefFib_zero_one_of_nonneg
end

section
section
set_option maxSynthPendingDepth 1

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem slX_lower_of_stokesAt (hZ : ZhangLowerX.Statement) {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
    [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E}
    {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting D O Lt) (Ch Cu : ℝ)
    (hII : IsIntersectionSystem II) (hpos : CuspBundlePos X) (hconj : MUConjInvariant X)
    (hint : HtInterior Ch X) (hbd : HtBoundary Ch X) (hmean : CuspMean Cu X) (hdeg : 0 < degMu X.H)
    (hN : 3 * D.j' + 1 ≤ D.N) (B : ℕ) (hB1 : 4 * D.f + 2 ≤ B) (hB2 : 4 * D.f * D.N ^ 2 ≤ B)
    (hS : StokesAt X B) :
    -((Ch + Cu / 2) * D.f * D.j' * X.La B) ≤ slX X B := by
  set a : ℝ := -(Ch * D.f * D.j' * X.La B) with ha
  have hyp : StokesLimit.Hyp X B a := by
    intro p q hp hpq
    have hq0 : 0 < q := by omega
    have hq : (0 : ℝ) < q := Nat.cast_pos.2 hq0
    obtain ⟨t₁, ht₁, hpos'⟩ := hpos B p q hB1 hp hpq
    obtain ⟨t₂, ht₂, hconj'⟩ := hconj B p q hB1 hp hpq
    obtain ⟨t₃, ht₃, hint'⟩ := hint B p q hB2 hp hpq
    obtain ⟨t₄, ht₄, hbd'⟩ := hbd B p q hB2 hp hpq
    refine ⟨min (min t₁ t₂) (min t₃ t₄), lt_min (lt_min ht₁ ht₂) (lt_min ht₃ ht₄), fun t' ht0 ht1 => ?_⟩
    have h1 : t' ≤ t₁ := ht1.trans ((min_le_left _ _).trans (min_le_left _ _))
    have h2 : t' ≤ t₂ := ht1.trans ((min_le_left _ _).trans (min_le_right _ _))
    have h3 : t' ≤ t₃ := ht1.trans ((min_le_right _ _).trans (min_le_left _ _))
    have h4 : t' ≤ t₄ := ht1.trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hsemi, hnef, -⟩ := hpos' t' ht0 h1
    have hz := hZ K ι (mCoordIdeal D.y) (mCoordIdeal D.y) D.n (X.MUq B p q t')
      ((q : ℝ) * (a - (p : ℝ) / q * D.KA)) II hII D.arith le_rfl hsemi hnef
      (hconj' t' ht0 h2) (fun W hW hXW => by
        have hh : a - (p : ℝ) / q * D.KA ≤ htMUc X.H X.S' B p q t' W := by
          by_cases hoff : OffBoundary D.Bd W
          · exact hint' t' ht0 h3 W hW hXW hoff
          · exact hbd' t' ht0 h4 W hW hXW hoff
        have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
        have e : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height (II K ι) (X.MUq B p q t') W =
            (q : ℝ) * htMUc X.H X.S' B p q t' W := by
          simp only [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.height, htMUc, ComponentSetting.MUq]
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_left hh hq.le)
    simp only [topMUc, geomDegMUc]
    rw [le_div_iff₀ (pow_pos hq _)]
    have e : ((D.n + 1 : ℕ) : ℝ) * (a - (p : ℝ) / q * D.KA) *
        (geomDeg (mCoordIdeal D.y) (MUc X.H X.S' B p q t') D.n / (q : ℝ) ^ D.n) * (q : ℝ) ^ (D.n + 1) =
        ((D.n + 1 : ℕ) : ℝ) * ((q : ℝ) * (a - (p : ℝ) / q * D.KA)) *
          geomDeg (mCoordIdeal D.y) (MUc X.H X.S' B p q t') D.n := by
      rw [pow_succ]
      field_simp
    rw [e]
    exact hz
  have h6 := hS a hyp
  have hj' : 1 ≤ D.j' := by
    have := D.j_le
    have := D.two_le_N
    simp only [ComponentData.j']
    omega
  have hm := hmean hj' hN B hB2
  have hn : (0 : ℝ) < ((D.n + 1 : ℕ) : ℝ) * degMu X.H := mul_pos (by positivity) hdeg
  rw [slX, le_div_iff₀ hn]
  have hm' := mul_le_mul_of_nonneg_left hm hn.le
  nlinarith

theorem ppc_lower_of_setting (hZ : ZhangLowerX.Statement) {II : IntersectionSystem} (hII : IsIntersectionSystem II)
    {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} [Nonempty Ψ] (T : RootTower Ψ N) {Ch Cu rd Lval : ℝ}
    (hvol : ∀ c, 0 < T.vol c) (hN : 3 * (N - T.j) + 1 ≤ N) {B : ℕ} (hB : 4 * Fintype.card Ψ * N ^ 2 ≤ B)
    {c : T.Comp} (h : T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) :
    -((Ch + Cu / 2) * Fintype.card Ψ * (min T.j (N - T.j) : ℕ) * bigLam B rd Lval) *
        (((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j)) ≤ T.PPc II B c (testPoly T.j) := by
  obtain ⟨K, _, ι, _, Ω, _, _, E, _, _, D, O, Lt, _, _, _, X, hDN, hDj, hrd, hL, h1, h2, h3, h4, h5, h6, -, h7, h8⟩ := h
  have hJ : 0 < testDeg Ψ N T.j := (GlobalTheory.T.test_polynomial_shift_total Ψ N T.j T.j_pos T.j_lt).2.1
  have hf : D.f = Fintype.card Ψ := rfl
  have hj' : D.j' = N - T.j := by simp only [ComponentData.j', hDN, hDj]
  have hmin : min T.j (N - T.j) = N - T.j := by
    have := T.j_lt
    omega
  have hcard : 1 ≤ Fintype.card Ψ := Fintype.card_pos
  have hN2 : 2 ≤ N := by
    have := T.j_pos
    have := T.j_lt
    omega
  have hsq : 4 * Fintype.card Ψ * 4 ≤ 4 * Fintype.card Ψ * N ^ 2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  have hB1 : 4 * D.f + 2 ≤ B := by
    rw [hf]
    omega
  have hB2 : 4 * D.f * D.N ^ 2 ≤ B := by rwa [hf, hDN]
  have hN' : 3 * D.j' + 1 ≤ D.N := by rwa [hj', hDN]
  have hl := slX_lower_of_stokesAt hZ X Ch Cu hII h1 h2 h3 h4 h5 h6 hN' B hB1 hB2 h7
  have hLa : X.La B = bigLam B rd Lval := by
    simp only [ComponentSetting.La, abelian₂, bigLam, hrd, hL]
  rw [hLa, hf, hj'] at hl
  rw [h8, hmin]
  have hw : (0 : ℝ) < ((dimX Ψ N T.j : ℝ) + 1) * (T.vol c * testDeg Ψ N T.j) :=
    mul_pos (by positivity) (mul_pos (hvol c) hJ)
  exact mul_le_mul_of_nonneg_right hl hw.le

theorem slope_lower_of_base_settings : ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ),
    T.Proportional → 3 * (N - T.j) + 1 ≤ N →
    (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c,
      T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) →
    T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  intro hZ II hII Ψ _ _ N _ T Ch Cu rd Lval hP hN hset B hB1 hB2 hB3
  rw [RootTower.PPt, RootTower.volT, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => ppc_lower_of_setting hZ hII T hP.1 hN hB2 (hset B hB1 hB2 hB3 c)

end GlobalTheory.CompanionTheory.Ar.Top
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_lower_base_settings : GroundTheory.Heights₂.Heights.LowerBoundFree.ZhangLowerX.Statement → ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (Ch Cu rd Lval : ℝ), T.Proportional → 3 * (N - T.j) + 1 ≤ N → (∀ B : ℕ, 128 ≤ B → 4 * Fintype.card Ψ * N ^ 2 ≤ B → T.bad.card ≤ B → ∀ c, T.HasBaseDegreeSettingStrict II Ch Cu rd Lval B c) → T.SlopeLower II (Ch + Cu / 2) rd Lval := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Top.slope_lower_of_base_settings
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem slopeLower_mono_top {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : Top.RootTower Ψ N)
    (II : IntersectionSystem) {C C' rd Lval : ℝ} (hCC : C ≤ C') (hrd : 1 ≤ rd) (hP : T.Proportional)
    (h : T.SlopeLower II C rd Lval) : T.SlopeLower II C' rd Lval := by
  intro B hB hB' hbad
  have h1 := h B hB hB' hbad
  have hJ : 0 < Top.testDeg Ψ N T.j := (GlobalTheory.T.test_polynomial_shift_total Ψ N T.j T.j_pos T.j_lt).2.1
  have hvol : 0 ≤ T.volT := Finset.sum_nonneg fun c _ => (hP.1 c).le
  have hB1 : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hL : 0 ≤ Top.bigLam B rd Lval := by
    unfold Top.bigLam
    have h2 : (1 : ℝ) ≤ B * rd := by nlinarith
    have := Real.log_nonneg h2
    positivity
  have hK : 0 ≤ (Fintype.card Ψ : ℝ) * ((min T.j (N - T.j) : ℕ) : ℝ) * Top.bigLam B rd Lval *
      (((Top.dimX Ψ N T.j : ℝ) + 1) * (T.volT * Top.testDeg Ψ N T.j)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hCC hK]

theorem volumeTheoremX_of_inputs : Top.Given → PtsIntegrableStatement → Out.WeilSt → (∃ Ch Cu : ℝ, NineGeoU Ch Cu) →
    HodgeLatticeFlagBound → TrivFlagOnHodge → Fl.FlatDegree → TwistAut → Cmp.CmpPair → Cmp.CmpSt → Top.VolumeTheoremX := by
  intro hG hPts hW hNineE hM3 hTF hFD hTw hCP hCS
  obtain ⟨Ch, Cu, hNine⟩ := hNineE
  obtain ⟨-, -, -, -, -, -, -, -, -, hIn, hHS, -, hNF, hAP⟩ := id hG
  obtain ⟨hZ1, hZ2, -⟩ := hHS
  obtain ⟨hZh, -, -, -, hGr⟩ := hNF
  have hAg := GlobalTheory.T.agreement_positive
  refine ⟨2 * max (Ch + Cu / 2) 0 + 3 * 4 + 5, by positivity, ?_⟩
  intro E _ _ _ _ H D Xo l c Y _ T o II hGl hX hII hq hpq hbad
  obtain ⟨hrd, hne, -⟩ := GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers E H
  haveI := hne
  have hp : 1 ≤ D.p := by omega
  have hqp : D.q ≤ D.p := by omega
  have hUnif := GlobalTheory.T.good_tower_real_agreement hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hProp : T.Proportional := GlobalTheory.T.real_tower_proportional GlobalTheory.T.proportional' hIn II hII _ _ T _ hUnif
  have hCI := GlobalTheory.T.real_tower_conv_I2 hAg hIn II hII _ _ T (Top.realOf o.toTowerOrigin)
  have hI1 := GlobalTheory.T.real_tower_I1 GlobalTheory.T.coefficients' hAg hIn II hII _ _ T _
    (GlobalTheory.T.good_tower_real_I6 hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hPos : (Top.realOf o.toTowerOrigin).Pos := fun a => (o.Fx a).pos
  have hA1 := GlobalTheory.T.real_tower_A1 hIn II hII _ _ T _ o.smooth o.flat hPos
  have hM1 := GlobalTheory.T.good_tower_M1_nef hG E H D Xo l c Y T o II hGl hII hp hq
  have hM2 := GlobalTheory.T.good_tower_M2 hG E H D Xo l c Y T o II hGl hII hp hq
  have hAN : T.ANef := fun B a => GlobalTheory.T.root_model_nef_fibres _ _ (T.M B a) fun k => by
    obtain ⟨h1, h0⟩ := (o.Or B a).A_deg
    by_cases hk : k = (o.Or B a).k₀
    · rw [hk, h1]; norm_num
    · rw [h0 k hk]
  have hI56 := GlobalTheory.T.good_tower_I5 hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hI7 : T.I7 := fun B a =>
    ⟨(GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T _ o.smooth o.flat B a).1,
      (GlobalTheory.T.real_tower_nef_general GlobalTheory.T.nef_polarization hIn II hII _ _ T _ o.smooth o.flat B a).2,
      GlobalTheory.T.good_tower_real_conditions hG E H D Xo l c Y T o II hGl hX hII hp hq B a⟩
  have hI8 := GlobalTheory.T.full_intersection_tower_I8_identity hCS hG hW E H D Xo l c Y T o II hX hII hp hq
  obtain ⟨φ, hfs, hLk⟩ := GlobalTheory.T.good_tower_global_conditions hCS hAg hM3 hTF hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hP6 := GlobalTheory.T.linked_tower_power_sum _ _ T II hII.1 hProp φ hLk
  have hPA := GlobalTheory.T.good_tower_propA_of_global_extra hAg hTw hCP hG E H D Xo l c Y T o II hGl hX hII hp hq
  have hbadP : ∀ p ∈ T.bad, p.Prime := fun p hp' => ((o.bad_iff p).1 hp').1
  have hPF := GlobalTheory.T.PropFTop_holds hPts hIn.2.2.1.2 hIn.2.1.2.1 _ _ T II _ (hostRd E) (hostLval H) hII.1 hCI.1 hProp hP6
    (by linarith) hbadP (GlobalTheory.T.good_tower_real_extra hFD hG E H D Xo l c Y T o II hGl hX hII hp hq)
  have hVol := GlobalTheory.T.good_tower_intersection_extra hCS hG E H D Xo l c Y T o II hGl hX hII hq hpq
  have hj3 : 3 * (D.p + D.q - T.j) + 1 ≤ D.p + D.q := by rw [o.j_eq]; omega
  have hSL0 := GlobalTheory.T.slope_lower_base_settings hZh II hII.1 _ _ T Ch Cu (hostRd E) (hostLval H) hProp hj3
    fun B _ hB _ a => GlobalTheory.T.base_setting_of_good_tower Ch Cu hNine hW hAg GlobalTheory.T.proportional' hCS hG hPts E H D Xo l c Y T o II hGl hX hII
      hp hq hqp hbad B hB a
  have hSL := slopeLower_mono_top T II (le_max_left (Ch + Cu / 2) 0) (by linarith) hProp hSL0
  have hch := GlobalTheory.T.tower_weil_inputs_combined GlobalTheory.T.flag_height hIn hZ1 hZ2 hAP hGr II hII _ _ T _ (max (Ch + Cu / 2) 0) 4 (hostRd E)
    (hostLval H) (le_max_right _ _) (by norm_num) (by linarith) hfs hProp hI1 hCI.2 hA1 hM1 hM2 hAN hI56.1 hI56.2
    hI7 hI8 hP6 hPA hPF hVol hSL
  exact ⟨hProp, hVol, hch.1, hch.2.1, hch.2.2.1, hch.2.2.2⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_theorem_of_inputs : Top.Given → PtsIntegrableStatement → Out.WeilSt → (∃ Ch Cu : ℝ, NineGeoU Ch Cu) → HodgeLatticeFlagBound → TrivFlagOnHodge → Fl.FlatDegree → TwistAut → Cmp.CmpPair → Cmp.CmpSt → Top.VolumeTheoremX := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.volumeTheoremX_of_inputs
end
