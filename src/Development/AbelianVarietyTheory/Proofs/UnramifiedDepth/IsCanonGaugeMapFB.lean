import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.HostTraceIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange

section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.FormalLog

theorem eq_zero_or_single_of_degree_le_one {σ : Type} (μ : σ →₀ ℕ) (h : μ.degree ≤ 1) :
    μ = 0 ∨ ∃ s, μ = Finsupp.single s 1 := by
  classical
  by_cases h0 : μ = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h0
    have hs' : 1 ≤ μ s := Nat.one_le_iff_ne_zero.2 hs
    have hle : Finsupp.single s 1 ≤ μ := Finsupp.single_le_iff.2 hs'
    obtain ⟨ν, rfl⟩ := exists_add_of_le hle
    rw [map_add, Finsupp.degree_single] at h
    have : ν = 0 := (Finsupp.degree_eq_zero_iff ν).1 (by omega)
    exact ⟨s, by rw [this, add_zero]⟩

theorem exists_log_exp :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d), ∃ lg ex : Pt k 1 d, (∀ i (μ : Fin 1 × Fin d →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (lg i) = MvPowerSeries.coeff μ (MvPowerSeries.X ((0 : Fin 1), i) : PS k 1 d)) ∧ (∀ i, ev (n := 2) ![addOf G.F (pt k d 0) (pt k d 1)] (lg i) = ev (n := 2) ![pt k d 0] (lg i) + ev (n := 2) ![pt k d 1] (lg i)) ∧ (∀ i, MvPowerSeries.constantCoeff (ex i) = 0) ∧ comp1 lg ex = pt k d 0 ∧ comp1 ex lg = pt k d 0 := by
  intro k _ _ d G
  obtain ⟨lg, h0, h1, hadd⟩ := logSt_and_logDerivSt.1 k d G
  obtain ⟨ex, -, he, ha, hb⟩ := GlobalTheory.ChartInv.exists_isInvPair k d lg h0 (by rw [h1]; simp)
  refine ⟨lg, ex, ?_, fun i => congrFun hadd i, he, ha, hb⟩
  intro i μ hμ
  rcases eq_zero_or_single_of_degree_le_one μ hμ with rfl | ⟨⟨a, j⟩, rfl⟩
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0, MvPowerSeries.coeff_zero_X]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    have hc := congrFun (congrFun h1 i) j
    simp only [dLin] at hc
    rw [hc, MvPowerSeries.coeff_X, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · have : Finsupp.single ((0 : Fin 1), j) 1 ≠ Finsupp.single ((0 : Fin 1), i) 1 := by
        intro h
        have := Finsupp.single_left_injective (one_ne_zero (α := ℕ)) h
        exact hij (Prod.mk.inj this).2.symm
      rw [if_neg hij, if_neg this]

end GlobalTheory.FormalLog
end

section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.ChartBaseChange

theorem isCanonGauge_mapFB {R k : Type} [CommRing R] [Algebra ℚ R] [CommRing k] [Algebra ℚ k]
    (f : R →+* k) {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {h : PS R 2 d}
    (hg : B.IsCanonGauge R h) :
    (GlobalTheory.FBMap.mapFB f B).IsCanonGauge k (MvPowerSeries.map f h) := by
  letI : Algebra R k := f.toAlgebra
  have h1 : B.IsCanonGauge k (MvPowerSeries.map f h) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId R k) hg
  have hid : ∀ {σ : Type} (g : MvPowerSeries σ k), MvPowerSeries.map (algebraMap k k) g = g := by
    intro σ g
    ext m
    simp [MvPowerSeries.coeff_map]
  have hF : (GlobalTheory.FBMap.mapFB f B).FK k = B.FK k := funext fun i => hid _
  have hA : ∀ a, (GlobalTheory.FBMap.mapFB f B).actK k a = B.actK k a := fun a => funext fun i => hid _
  refine ⟨h1.ax0, h1.ax1, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hF, ← h1.ph1]; exact hid _
  · rw [hF, ← h1.ph2]; exact hid _
  · rw [← h1.sy]; exact hid _
  · rw [hA, hA, ← h1.ad a]; exact hid _

theorem intS_map {T : CDVR} {C : Type} [Field C] {V : VF C} {ι : T.Fr →+* C} (hι : EmbOK T V ι)
    {σ : Type} {g : MvPowerSeries σ T.Fr} {g0 : MvPowerSeries σ T.V}
    (hg : g = MvPowerSeries.map (algebraMap T.V T.Fr) g0) : IntS V (MvPowerSeries.map ι g) := by
  intro m
  rw [hg, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
  exact (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1 _

theorem exists_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.BCExSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ T io y C3 C _ _ V ι hι hac hcpl hl hw k hk
  obtain ⟨gF, gA, g1, g2, gs, ga, -⟩ := C3.gen.1
  have hg : (a3B C3).IsCanonGauge T.Fr (a3h C3) := by
    letI := io.toAlgebra
    exact C3.ch.gauge
  obtain ⟨lg, ex, hlin, hadd, hc, hle, hel⟩ :=
    GlobalTheory.FormalLog.exists_log_exp C (chD C3.ch) (GlobalTheory.FBMap.mapFB ι (a3B C3)).G
  exact ⟨{ algClosed := hac
           cpl := hcpl
           l_odd := hl
           B := GlobalTheory.FBMap.mapFB ι (a3B C3)
           h := MvPowerSeries.map ι (a3h C3)
           gauge := isCanonGauge_mapFB ι (a3B C3) hg
           intF := fun i => intS_map hι (gF i)
           intAct := fun a i => intS_map hι (gA a i)
           intPh1 := intS_map hι g1
           intPh2 := intS_map hι g2
           intSy := intS_map hι gs
           intAd := fun a => intS_map hι (ga a)
           lg := lg
           lg_lin := hlin
           lg_add := hadd
           ex := ex
           ex_const := hc
           lg_ex := hle
           ex_lg := hel
           w0 := H.w0
           halfIntegralGenerator_add_conj_eq_one := hw
           k := k
           k_unit := hk },
    ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩⟩

end GlobalTheory.ChartBaseChange
end
