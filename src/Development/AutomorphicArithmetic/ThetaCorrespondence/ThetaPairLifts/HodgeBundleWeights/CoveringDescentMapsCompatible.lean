import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsBoundOfDeepGood
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstant
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortGeneratorNormComparison
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspRegularLevelDeterminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstantStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.DeepLatticeEqLevelLatticeOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsBoundOfDeepGoodStatement

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.ShortDet
section Weight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
end Weight
set_option maxHeartbeats 1600000 in
theorem exists_short_integral_vector : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → 8 ≤ D.R.f → 100 ≤ D.R.r → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂), ∃ u : Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), u ∈ AllWt.latW Y.U _ ∧ (∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ (grpHR fr) u * f = 0 → f = 0) ∧ ∀ (γ : (LevelAut (T.Q.Dw j) Y.d.l₂)) (G : WTZ D.host.E) (f : Y.V G) (g : Y.V (G + (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0))), Even G.2 → (g : Rul Y.d.Xo₂ Y.d.c₂) = f * pull Y.d.Xo₂ Y.d.c₂ γ u → ∀ σ, Y.nrm _ σ g ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 9) * Y.nrm G σ f := by
  intro hP hGr hQ hS hK hN
  obtain ⟨C₁, hC₁, hb⟩ := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  obtain ⟨C₃, hC₃, h3⟩ := _root_.GlobalTheory.T.short_generator_norm_comparison hP
  refine ⟨C₃ + 240 + C₁ + 2 * C₃, by positivity, ?_⟩
  intro D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' he hg hf hr fr
  obtain ⟨-, -, -, -, -, hdeg, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hT.pins
  obtain ⟨hpq, -, -⟩ := hJ j hj
  obtain ⟨hp', hq', -⟩ := hT.pins.2.2.2 j hj
  obtain ⟨-, h0, hcz⟩ := cZero_spec D j
  have hgap : ((8 * D.R.f * D.R.r + 10 : ℕ) : ℤ) ≤ cZero D j := by
    have h1 := (cZeroN_isLeast D j).1.2.1
    have h2 := le_choose hf hr hp hq hpq
    rw [hp', hq'] at h2
    exact Int.ofNat_le.2 (by omega)
  have hanti := antitone_smul_hodgeWt (T.Q.Dw j) h0
  have hgp := gap_smul_hodgeWt (T.Q.Dw j) hp hq (cZero D j)
  have hsz := size_smul_hodgeWt (T.Q.Dw j) h0
  have hcard := card_levelAut_le (T.Q.Dw j) Y.d.l₂
  rw [hdeg, congrArg (Nat.cast : ℕ → ℝ) hpq] at hsz
  rw [hdeg, hpq, Nat.mul_div_cancel_left _ two_pos] at hcard
  have hf' : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hr' : (100 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hcz' : (cZero D j : ℝ) ≤ 22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4 := by exact_mod_cast hcz
  have hs0 : 0 ≤ ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| := by positivity
  have hb' := hb D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho _ hanti
  have h3' := h3 D T hT j hp hq hE hj Y e o hG Lb hL hM hF hfr ho c₁ hc hc' _ hanti fun τ => (hgp τ).symm ▸ hgap
  generalize ∑ τ, ∑ k, |((cZero D j • hodgeWt (T.Q.Dw j)) τ k : ℝ)| = s at hs0 hsz hb' h3'
  have ha : (1 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
  have hs : s ≤ ((D.R.f : ℝ) * D.R.r) ^ 5 := by
    refine hsz.trans ?_
    push_cast
    calc _ ≤ 2 * (D.R.f : ℝ) * (D.R.r * (22 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 4)) := by gcongr
      _ = 44 * ((D.R.f : ℝ) ^ 3 * (D.R.r : ℝ) ^ 5) := by ring
      _ ≤ (D.R.f : ℝ) ^ 2 * ((D.R.f : ℝ) ^ 3 * (D.R.r : ℝ) ^ 5) := by gcongr; nlinarith
      _ = _ := by ring
  have hls : Real.log s ≤ 5 * Lb := by
    rcases hs0.eq_or_lt with rfl | h
    · rw [Real.log_zero]; linarith
    · refine (Real.log_le_log h hs).trans ?_
      rw [Real.log_pow]; push_cast; linarith
  have hcard' : (Nat.card (grpHR fr) : ℝ) ≤ Real.exp (120 * ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb) := by
    have h1 : (Nat.card (grpHR fr) : ℝ) ≤ (Y.d.l₂.M : ℝ) ^ (2 * (D.R.f * D.R.r)) ^ 2 := by
      exact_mod_cast (Subgroup.card_le_card_group _).trans hcard
    refine h1.trans ((pow_le_pow_left₀ (by positivity) ((Real.le_exp_log _).trans (Real.exp_le_exp.2 hM)) _).trans ?_)
    rw [← Real.exp_nat_mul]
    push_cast
    exact le_of_eq (by congr 1; ring)
  have haZ : (D.R.f : ℝ) * D.R.r ≤ D.R.f * D.R.r * Lb := le_mul_of_one_le_right (by positivity) hL
  have hZ2 : ((D.R.f : ℝ) * D.R.r) ^ 2 * Lb ≤ (D.R.f * D.R.r * Lb) ^ 2 := by
    rw [mul_pow _ Lb]; gcongr; nlinarith
  replace hs := hs.trans (pow_le_pow_left₀ (by positivity) haZ 5)
  have hZ := ha.trans haZ
  rw [mul_assoc] at hcard'
  generalize (D.R.f : ℝ) * D.R.r * Lb = Z at hb' h3' hs hZ hZ2 ⊢
  have hw : ∀ k, k ≤ 9 → Z ^ k ≤ Z ^ 9 := fun k hk => pow_le_pow_right₀ hZ hk
  have hA : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hG.lev.2]; exact Nat.coprime_one_left _
  have hpos : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by omega
  obtain ⟨u₀, h₀, hd₀⟩ := _root_.GlobalTheory.T.orbits_separated_by_regular_cusp hP hGr hQ hS hK hN D T hT j hp hq hE hj Y e o hG he hg fr _ (Or.inl rfl)
  obtain ⟨u, hu, hd, hsup⟩ := exists_short (β := Real.exp (C₁ * Z ^ 3)) (Λ := Real.exp (2 * C₃ * Z ^ 9))
    (N := Real.exp (C₃ * Z ^ 3)) hpos hA hG.unf (grpHR fr) _ (Real.one_le_exp (by positivity)) (Real.exp_pos _).le
    (Real.exp_pos _).le (fun W => (hb' (by linarith) W).2.1)
    (fun W => ((_root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hE hj Y e o hG _ hanti fun τ => by rw [hgp]; omega).2 W).2.2)
    (fun W => by
      obtain ⟨n, w, abelian₂, a1, a2, a3⟩ := h3' (by linarith) W
      refine ⟨n, w, abelian₂, a1, (Real.le_exp_log _).trans (Real.exp_le_exp.2 (a2.trans ?_)),
        (Real.le_exp_log _).trans (Real.exp_le_exp.2 a3)⟩
      have h1 : Z ^ 3 * s ≤ Z ^ 8 := (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
      have h2 := hw 8 (by norm_num)
      have h4 := hw 5 (by norm_num)
      rw [mul_comm 2, mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) hC₃) h₀ hd₀
  refine ⟨u, hu, hd, normW_mul_pull_le hpos hA (fun σ hσ => ?_) (fun G hGe => ?_) (AllWt.even_wtOf _ _) (Real.exp_pos _).le
    fun σ z => (hsup σ z).trans ?_⟩
  · obtain ⟨th, hr, -, h⟩ := hG.dictU σ hσ
    exact h.2.2.2.1
  · obtain ⟨k₁, k₂⟩ := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm D T hT j hp hq hE hj Y e o hG G hGe
    exact ⟨k₁, fun γ f g h => (k₂ γ f g h).2⟩
  · refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcard' 2)
      (by positivity)) (by positivity)).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have h1 := mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₁
    have h2 := mul_le_mul_of_nonneg_left (hw 3 (by norm_num)) hC₃
    have h4 := hw 2 (by norm_num)
    push_cast
    linarith
end GlobalTheory.ShortDet
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_short_integral_vector_of_determinant_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → |c₁| ≤ 9 * D.R.r * Lb → 4 ≤ e → (∀ k, D.R.r + 1 < D.host.g k) → 8 ≤ D.R.f → 100 ≤ D.R.r → ∀ (fr : TypeFrame (T.Q.Dw j) Y.d.l₂), ∃ u : Y.V (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0), u ∈ AllWt.latW Y.U _ ∧ (∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂, levDet Y.d.Xo₂ Y.d.c₂ (grpHR fr) u * f = 0 → f = 0) ∧ ∀ (γ : (LevelAut (T.Q.Dw j) Y.d.l₂)) (G : WTZ D.host.E) (f : Y.V G) (g : Y.V (G + (wtOf (T.Q.Dw j) (cZero D j • hodgeWt (T.Q.Dw j)) 0))), Even G.2 → (g : Rul Y.d.Xo₂ Y.d.c₂) = f * pull Y.d.Xo₂ Y.d.c₂ γ u → ∀ σ, Y.nrm _ σ g ≤ Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 9) * Y.nrm G σ f := by
  first | exact @_root_.GlobalTheory.ShortDet.exists_short_integral_vector | exact _root_.GlobalTheory.ShortDet.exists_short_integral_vector | (intros; apply _root_.GlobalTheory.ShortDet.exists_short_integral_vector <;> assumption)
end
end

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
namespace GlobalTheory.CovTop.DescentMaps
end GlobalTheory.CovTop.DescentMaps
namespace GlobalTheory.CovTop.DescentMaps
set_option maxHeartbeats 1000000 in
theorem covering_descent_maps_compatible : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral →
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Gram → DeepGood → Size → FlatDeg → Maps := by
  intro hP hGD hQ hSI hTF hSN hGram hDG hSz hFD
  obtain ⟨C, hC0, hub⟩ := _root_.GlobalTheory.T.exists_short_integral_vector_of_determinant_bound hP hGD hQ hSI hTF hSN
  have hT := _root_.GlobalTheory.T.type_lattice_deep_level_eq hP hGram hDG
  have hS := GlobalTheory.T.size_bounds_for_family hSz
  have hH := GlobalTheory.CovTop.Sizes.hostN (2 * C + 200)
  unfold Maps Covers Lifts
  unfold DeepGood at hDG
  unfold FlatDeg at hFD
  unfold Covers Lifts at hT hS hDG hFD
  unfold HostN Lifts at hH
  refine Closed.imp ((((hT.and hS).and hH).and hDG).and hFD) ?_
  intro eps Fm CH _ hall0
  obtain ⟨⟨⟨⟨⟨C1, -, hT'⟩, ⟨C2, -, hS'⟩⟩, ⟨A, -, hH'⟩⟩, ⟨C4, -, hDG'⟩⟩, ⟨C5, -, hFD'⟩⟩ := hall0
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hall⟩ := (((hT'.and hS').and hH').and hDG').and hFD'
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := hall x hx hle ι p hp
  obtain ⟨fr, ψ, -, hl, hlat, hcard⟩ := a1 i hi Y hY
  obtain ⟨hLaws, hInR, hL1, hM, hE, hfr, hexp, hg, hf8, hr100, hflat, -⟩ := a2 i hi Y hY
  have hN := a3 i
  have hDGY := a4 i hi Y hY
  have hFDY := a5 i hi Y hY
  obtain ⟨-, hpq, hq, h2q⟩ := GlobalTheory.Member.exists_iotaOK (Fm.D x ι) p.T.Q hLaws.pins ((i : ℕ) + 1) hInR
  have hq1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).q := by
    rw [hq]; simp only [Formalism.MainNotions.WeightFamilies.rho, Formalism.BasicNotions.Ranks.sigW]; omega
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by omega
  have hfin : 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 := by rw [hN.deg]; omega
  obtain ⟨u, hu, hdet, hB⟩ := hub (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1 (Fm.L x ι).sc.L hL1
    hM hE hfr (le_of_eq rfl) _ hFDY (by rw [abs_neg]; exact hflat) hexp hg hf8 hr100 fr
  have hK := GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY.1
  have hGk : Even (Gk p i).2 := (p.κ i).n_even.natCast
  have hW : Even (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0).2 :=
    GlobalTheory.AllWt.even_wtOf _ _
  have hGm : Even (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))).2 := hGk.add (GlobalTheory.AllWt.even_wtOf _ _)
  have hGW : Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))) +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 = Gk p i := by
    simp only [Gs, shiftG, add_assoc, ← GlobalTheory.AllWt.wtOf_add, neg_smul, neg_add_cancel, add_zero, GlobalTheory.AllWt.wtOf_zero]
  set z := zBase (Fm.L x ι) with hz
  have hzL : (Fm.L x ι).sc.L ≤ z := by
    have h8 : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have h100 : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have h0 : (0 : ℝ) ≤ (Fm.L x ι).sc.L := by linarith
    rw [hz, zBase]
    nlinarith [mul_le_mul h8 h100 (by norm_num) (by linarith)]
  have hz1 : 2 * C + 200 ≤ z := hN.big.1.trans hzL
  have hPP : z ^ 12 ≤ (Fm.L x ι).sc.b := by
    have h1 := hN.ppLow
    obtain ⟨hA1, hA2, -⟩ := hN.poly
    have h3 := hN.room
    have hz0 : 1 ≤ z := by linarith
    have hx1 : 1 ≤ (Fm.L x ι).sc.x ^ A := le_trans (one_le_pow₀ hz0) (h1.trans hA2)
    have h4 : (Fm.L x ι).sc.x ^ A ≤ ((Fm.L x ι).sc.x ^ A) ^ (2 * C + 200) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hx1 (show (1 : ℝ) ≤ 2 * C + 200 by linarith)
    linarith
  have hb : (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (C * ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 9) ^ 2 ≤
      Real.exp (2 * (Fm.L x ι).sc.b) := by
    have hz9 : ((Fm.D x ι).R.f * (Fm.D x ι).R.r * (Fm.L x ι).sc.L : ℝ) = z := by rw [hz, zBase]
    rw [hz9]
    rw [Nat.card_eq_fintype_card] at hcard
    have hn0 : (0 : ℝ) < Fintype.card (grpHR fr) := by exact_mod_cast Fintype.card_pos
    have hz0 : 1 ≤ z := by linarith
    have hn3 : (Fintype.card (grpHR fr) : ℝ) ^ 3 ≤ Real.exp (135 * z ^ 2) := by
      rw [← Real.exp_log (pow_pos hn0 3), Real.log_pow]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    have he : Real.exp (C * z ^ 9) ^ 2 = Real.exp (2 * C * z ^ 9) := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [he]
    calc (Fintype.card (grpHR fr) : ℝ) ^ 3 * Real.exp (2 * C * z ^ 9)
        ≤ Real.exp (135 * z ^ 2) * Real.exp (2 * C * z ^ 9) :=
          mul_le_mul_of_nonneg_right hn3 (Real.exp_pos _).le
      _ = Real.exp (135 * z ^ 2 + 2 * C * z ^ 9) := by rw [← Real.exp_add]
      _ ≤ Real.exp (2 * (Fm.L x ι).sc.b) := by
          refine Real.exp_le_exp.2 ?_
          have a1 : z ^ 2 ≤ z ^ 9 := pow_le_pow_right₀ hz0 (by norm_num)
          have a2 : z ^ 10 ≤ z ^ 12 := pow_le_pow_right₀ hz0 (by norm_num)
          have a3 : (135 + 2 * C) * z ^ 9 ≤ z * z ^ 9 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          have a4 : z * z ^ 9 = z ^ 10 := by ring
          nlinarith
  have e2 : Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1)) = Gk p i +
      wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0 := by
    unfold Gs Gk shiftG; rfl
  obtain ⟨n, φ, h1, h2, h3, h4⟩ := mapsCore (grpHR fr) (Nat.le_add_right_of_le hp1) hl.coprime
    (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1))))
    (wtOf (p.T.Q.Dw ((i : ℕ) + 1)) (cZero (Fm.D x ι) ((i : ℕ) + 1) • hodgeWt (p.T.Q.Dw ((i : ℕ) + 1))) 0) (Gk p i) hGW
    hGm hW (hK _ hGk).1 (hK _ hW).1 (fun γ f g hg => ((hK _ hGk).2 γ f g hg).1)
    (fun γ f g hg => ((hK _ hW).2 γ f g hg).1) (fun γ f g hg => ((hK _ hGk).2 γ f g hg).2)
    hDGY.1 hDGY.2.2.1 (GlobalTheory.LevDesc.chiHR fr ψ) u hu hdet _ (Real.exp_pos _).le
    (fun γ f g hg σ => hB γ _ f g hGm hg σ) _ hb (latDeep p i Y) hlat
    (Gs p i (cZero (Fm.D x ι) ((i : ℕ) + 1))) e2.symm
  exact ⟨n, φ, h1, h2, h3, h4⟩
end GlobalTheory.CovTop.DescentMaps
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_descent_maps_exist : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Gram → DeepGood → Size → FlatDeg → Maps := by
  first | exact @_root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible | exact _root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible | (intros; apply _root_.GlobalTheory.CovTop.DescentMaps.covering_descent_maps_compatible <;> assumption)
end
end
