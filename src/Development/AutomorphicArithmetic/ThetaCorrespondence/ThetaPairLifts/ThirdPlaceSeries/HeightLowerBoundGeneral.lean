import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightLowerBoundGeneral
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HeightAddLogNonneg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsShortSectionCoverHeight
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeometricOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrameStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarryingSectionIntegralFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfSizeLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSectionBoundedByBergmanKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeightStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHoldsStatement

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.HtTopG
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} {p : PtAt ex Csz} {i : Fin D.R.m} {Y : Cov p i}
end Point
theorem height_of_meanAll_bound : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovHt.ShortAlt → _root_.GlobalTheory.CovHt.GeometricCondition → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → D.R.m ^ 2 ≤ D.R.k → ∀ j : ℕ, 1 ≤ j → j < D.R.m → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → Y.d.l₂.M'.primeFactors.card ≤ 15 → MeanAll Y.U (xiR D) (ell D) C) →
    _root_.GlobalTheory.CovTop.HeightCondition := by
  intro hPX hP hDG hSz hDg hSh hGe hMu hBu hDS
  obtain ⟨C0, h0, hDS⟩ := hDS
  refine Closed.imp ((((((hDG.and hSz).and hDg).and hSh).and hGe).and hMu).and hBu) ?_
  intro eps Fm CH _ hF
  obtain ⟨⟨⟨⟨⟨⟨⟨C1, -, a1⟩, ⟨C2, -, a2⟩⟩, ⟨C3, -, a3⟩⟩, ⟨C4, c4, a4⟩⟩, ⟨C5, -, a5⟩⟩, ⟨C6, c6, a6⟩⟩, ⟨C7, c7, a7⟩⟩ := hF
  refine ⟨C4 + C6 + C7 + C0 * C7, by positivity, ?_⟩
  obtain ⟨x0, hall⟩ := ((((((a1.and a2).and a3).and a4).and a5).and a6).and a7)
  refine ⟨x0, fun x hx hle ι p hp i hm Y hY u1 hq => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hall x hx hle ι p hp
  have hDGa := b1 i hm Y hY
  obtain ⟨hb1, hbE, -, -, -, -, hρ⟩ := b2 i
  have hU : 0 ≤ unitE p := by linarith
  have hρ1 : rhoB (dat p i) u1 < 1 := ((hρ hm).2 u1 hq).2.2.1
  have hBu := b7 i hm Y hY u1 hq
  exact _root_.GlobalTheory.CovHt.HtTopG.heightAt_eq_of_cover hPX hP hY.1 (_root_.GlobalTheory.CovHt.cover_height_comparison hP _ _ _ _ _ _) h0 c4 c6 c7 hU
    (hDS _ p.T p.fw.laws (Formalism.BasicNotions.ParameterChoice'.m_sq_le_k (Fm.params x hx ι)) ((i : ℕ) + 1) (by omega) hm Y _ _ hY.1 hBu.1) hDGa.2.2.2.2.2.2.1 hρ1
    (b3 i hm Y hY u1 hq) (b4 i hm Y hY u1 hq) (b5 i hm Y hY u1 hq) (b6 i hm Y hY u1 hq) hBu
end GlobalTheory.CovHt.HtTopG
end
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.ShortPf
section Point
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
set_option maxHeartbeats 800000 in
theorem cover_height_short_section_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovHt.ShortAlt := fun hP _ _ hF => by
  obtain ⟨C, hC, H3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 1) _root_.GlobalTheory.CovTop.WtShape.wtN_z) hF) fun Fm _ _ h => ?_
  obtain ⟨⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩, ⟨_, _, h3⟩⟩ := h
  obtain ⟨x0, h⟩ := (h1.and h2).and h3
  refine ⟨C * 693, by positivity, x0, fun x hx hle ι p hp i hi Y hY u1 hq => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := h x hx hle ι p hp
  have hH := g1 i
  have hw := g2 i
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := weight_rows p i hH hw hi u1 hq
  have hL := hH.big.2.1
  have hM : Real.log Y.d.l₂.M ≤ 30 * (Fm.L x ι).sc.L := by
    rw [hY.1.lev.1.2.1, hY.1.pd, p.fw.laws.pins.2.1.1]
    exact log_level hH
  have key := H3 _ p.T p.fw.laws _ a1 a2 (by rw [hH.deg]; have := hH.f8; omega) ⟨by omega, hi.le⟩ Y _ _ hY.1 _ (by linarith) hM
    (fieldSz_host hH) hH.logfr.1 le_rfl _ (g3 i hi Y hY) (by rw [abs_neg]; exact FlatSz.abs_flatDegVal_le p i hH hw) u1 a3
    (fun τ => by
      unfold GlobalTheory.CompHS.gap
      rw [dif_pos (by show (dat p i).p - 1 + 1 < (dat p i).p + (dat p i).q; omega)]
      exact a4 τ _ _ rfl (by show (dat p i).p - 1 + 1 = _; omega)) a5
  refine ⟨Real.exp (C * ((((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 * (∑ τ, ∑ k, |(u1 τ k : ℝ)|) +
    (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 5)), fun Z => ?_, ?_⟩
  · obtain ⟨n, w, abelian₂, hs, hl, -⟩ := key Z
    have := (Real.log_le_iff_le_exp (lt_of_lt_of_le one_pos hs.one_le)).1 hl
    exact ⟨n, w, hs.gen, fun k σ => (hs.le k σ).trans this, hs.one_le.trans this⟩
  · rw [Real.log_exp, mul_assoc, mul_assoc C]
    exact mul_le_mul_of_nonneg_left a6 hC
end GlobalTheory.CovHt.ShortPf
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_short_of_deep_size_flatDeg : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovHt.ShortAlt := by
  first | exact @_root_.GlobalTheory.CovHt.ShortPf.cover_height_short_section_alt | exact _root_.GlobalTheory.CovHt.ShortPf.cover_height_short_section_alt | (intros; apply _root_.GlobalTheory.CovHt.ShortPf.cover_height_short_section_alt <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovHt.GeomBound
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem geom_of_prints_toroidal_deepGood_size : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.GeometricCondition := by
  intro hX hG hQ hP h1 h2 h3 _ hS
  have hH := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 0
  have hW := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovHt.GeometricCondition _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.SizeCondition _root_.GlobalTheory.CovTop.LiftsCondition at hS
  unfold _root_.GlobalTheory.CovTop.HostNAlt _root_.GlobalTheory.CovTop.LiftsCondition at hH
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at hW
  refine ((hS.and hH).and hW).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, hx0⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3⟩ := hx0 x hx hle ι p hp
  exact _root_.GlobalTheory.CovHt.GeomBound.geometric_height_bound_at_place p i hX hG hQ hP h1 h2 h3 (b1 i) (b2 i) (b3 i) hi Y hY u1 hu
end GlobalTheory.CovHt.GeomBound
end
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covHt_geom_of_siegel_toroidal_semiAbelian : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.GeometricCondition := by
  first | exact @_root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size | exact _root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size | (intros; apply _root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size <;> assumption)
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovMult
open GlobalTheory.SlopeRec GlobalTheory.FlatLine GlobalTheory.RefSum
section Places
variable {K : Type} [Field K] [NumberField K]
end Places
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
theorem multC_of_refW_alt : _root_.GlobalTheory.RefSum.ReferenceWeight → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition := by
  intro hR hK
  refine Closed.imp (Closed.and hR hK) fun _ _ _ ⟨⟨C₁, h₁, hR⟩, C₂, h₂, hK⟩ => ⟨C₁ + C₂, add_nonneg h₁ h₂, ?_⟩
  refine (hR.and hK).imp fun _ h x hx hle ι p hp i hi Y hY u1 hu => ?_
  obtain ⟨hR, hK⟩ := h x hx hle ι p hp
  obtain ⟨S, a, s, hS, hs, ha⟩ := hR i hi Y hY u1 hu
  obtain ⟨cc, hc0, hc, hZ⟩ := hK i hi Y hY u1 hu
  have hs0 : 0 ≤ s := (Finset.sum_nonneg fun q _ => mul_nonneg (hS.2.1 q) (Real.log_natCast_nonneg q)).trans hS.2.2.2
  exact ⟨cc + s, add_nonneg hc0 hs0, budget_add hs hc, fun Z => mult_of hY.1.unf hS ha (hZ Z)⟩
end GlobalTheory.CovMult
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrying_section_integral_frame_alt : _root_.GlobalTheory.RefSum.ReferenceWeight → (_root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP C => ∀ u1, Quo p i PP u1 → ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧ ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (θ : Rul Y.d.Xo₂ Y.d.c₂) (e : HeightOneSpectrum (𝓞 Y.d.c₂.F) →₀ ℝ) (t : (Y.d.c₂.F →+* ℂ) → ℝ), Carries Y.U Z u1 (uPrime (dat p i) u1) θ ∧ (∀ (la : HeightOneSpectrum (𝓞 Y.d.c₂.F)) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → ∀ y : IntFr Y.d.Xo₂ Y.d.c₂ T io, y.IsAlg → (∃ (G' : WTZ (Fm.D x ι).host.E), ∃ f ∈ cuspOn Y.U Z G', evI y f ≠ 0) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ((8 / 2500 * φ / e₀ - 8 * e la : ℝ) : EReal) ≤ nval T.V e₀ (evI y θ)) ∧ InfBd Y.U (xiR (Fm.D x ι)) (fun _ => (Fm.D x ι).sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) (wtOf (dat p i) ((8 : ℤ) • (u1 - uPrime (dat p i) u1)) 0) 8 θ t ∧ cost e t ≤ cc) → _root_.GlobalTheory.CovHt.MultiplicityConstantCondition := by
  atlas_forward_decl _root_.GlobalTheory.CovMult.multC_of_refW_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.BudgetPf
section Point
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem budget_alt : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := fun hH hW _ =>
  Closed.imp (Closed.and (hH 1) hW) fun _ _ _ ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => by
    obtain ⟨x0, h⟩ := h1.and h2
    exact ⟨83400, by norm_num, x0, fun x hx hle ι p hp i hi Y hY u1 hq =>
      budgetAt p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) hi Y hY u1 hq⟩
end GlobalTheory.CovHt.BudgetPf
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
theorem _root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := by
  atlas_forward_decl _root_.GlobalTheory.CovHt.BudgetPf.budget_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hostN_forall : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  first | exact @_root_.GlobalTheory.CovTop.Sizes.hostN_alt | exact _root_.GlobalTheory.CovTop.Sizes.hostN_alt | (intros; apply _root_.GlobalTheory.CovTop.Sizes.hostN_alt <;> assumption)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates
set_option maxHeartbeats 1000000 in
theorem height_lower_bound_general_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.HeightCondition :=
  fun hSB hX hGD hQ hP hH hD hG hS hDg hF => _root_.GlobalTheory.CovHt.HtTopG.height_of_meanAll_bound hSB hP hG hS hDg (_root_.GlobalTheory.T.covering_short_of_deep_size_flatDeg hP hG hS hF) (_root_.GlobalTheory.T.covHt_geom_of_siegel_toroidal_semiAbelian hX hGD hQ hP hH.sieg hX.ks hX.lie hG hS) (_root_.GlobalTheory.T.carrying_section_integral_frame_alt (_root_.GlobalTheory.T.refW_of_prints_deepGood_size_flatDeg hP hG hS hF) (_root_.GlobalTheory.T.exists_section_bounded_by_bergman_kernel_alt hP hH hG hS hF)) (_root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size _root_.GlobalTheory.T.hostN_forall _root_.GlobalTheory.T.lift_weight_numerator hS) hD
end SelfIntersectionVolumeEstimates
end
end
end
