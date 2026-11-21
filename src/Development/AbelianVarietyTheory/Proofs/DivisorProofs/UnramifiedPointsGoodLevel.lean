import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointMemClosed

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compositum_intermediateField_exists_place_valuation_eq : ∀ (F F' K : IntermediateField ℚ ℂ) [NumberField F] [NumberField F'] [NumberField K] (hF : F ≤ K), K = F ⊔ F' → ∀ q : ℕ, q.Prime → ¬ (q : ℤ) ∣ discr F' → ∀ w : HeightOneSpectrum (𝓞 F), ((q : ℕ) : 𝓞 F) ∈ w.asIdeal → ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ∀ a : F, vLa 𝔭 (IntermediateField.inclusion hF a) = vLa w a := by
  first | exact @GlobalTheory.UnramCompositum.exists_vLa_eq | exact GlobalTheory.UnramCompositum.exists_vLa_eq | (intros; apply GlobalTheory.UnramCompositum.exists_vLa_eq <;> assumption)
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (hle : c.F ≤ K), GlobalTheory.CompRat.CurveOver H K l.M' → ∀ Z : Comp Xo c, (letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra; ∃ y : FrPt Xo c K, LiesOn Z y) := by
  first | exact @GlobalTheory.FixedPoint.exists_frPt_liesOn | exact GlobalTheory.FixedPoint.exists_frPt_liesOn | (intros; apply GlobalTheory.FixedPoint.exists_frPt_liesOn <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.CompletionPoint

theorem exists_intFr_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  intro E _ _ _ H Dw l Xo c hpq hg Z K _ _ _ y hy w 𝔭 hv
  classical
  obtain ⟨hP, hN⟩ := GlobalTheory.Moduli.jointExistence_and_moduliScheme
  obtain ⟨O, _, β, Y, -, hPI, hbase⟩ := GlobalTheory.Frames.modelAtSt_of_good hP hN E H Dw l Xo c hpq hg w
  obtain ⟨T, k, hk, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K 𝔭
  have ho : OverLa w T.V (k.comp (algebraMap c.F K)) 1 :=
    ⟨Nat.one_pos, fun a => by rw [← hv a]; exact hk.2 _⟩
  obtain ⟨b, hb⟩ := hbase T _ 1 ho
  have hT := GlobalTheory.abelianSchemeLaws_all.2.secTwist
  have hIF : IntFramesSt Xo c := GlobalTheory.intFrames_of_laws GlobalTheory.abelianSchemeLaws_all.1.secBaseChange hT E H Dw l Xo c
  let _ := (k.comp (algebraMap c.F K)).toAlgebra
  have hz : ptF y ≫ Limits.pullback.snd _ _ = spMap (algebraMap c.F K) := Limits.pullback.lift_snd _ _ _
  have hs : (spMap k ≫ ptF y) ≫ Limits.pullback.snd _ _ = spMap (k.comp (algebraMap c.F K)) := by
    rw [Category.assoc, ← GlobalTheory.EtaVal.spMap_comp_spMap]
    exact congrArg _ hz
  have hx : ((spMap k ≫ ptF y) ≫ Limits.pullback.fst _ _) ≫ Xo.s = sOf c T.Fr := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hs, GlobalTheory.EtaVal.spMap_comp_spMap]
    rfl
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) _ hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y', t, hbor⟩ := intFr_of_model hIF T (k.comp (algebraMap c.F K)) Y hPI b hb y₀
  refine ⟨T, k.comp (algebraMap c.F K), y', ho, hfin, fun q => ?_⟩
  have h1 : y'.1.x = y₀.x := hbor.1
  have h2 : ptF y'.1 = spMap k ≫ ptF y := by
    apply Limits.pullback.hom_ext
    · exact (Limits.pullback.lift_fst _ _ _).trans (h1.trans h0)
    · exact (Limits.pullback.lift_snd _ _ _).trans hs.symm
  rw [h2]
  exact hy (spMap k q)

end GlobalTheory.CompletionPoint
end

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramedPoint_completion_index_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → ∀ (Z : Comp Xo c) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (w : HeightOneSpectrum (𝓞 c.F)) (𝔭 : HeightOneSpectrum (𝓞 K)), (∀ a : c.F, vLa 𝔭 (algebraMap c.F K a) = vLa w a) → ∃ (T : CDVR) (ι : c.F →+* T.Fr) (y' : IntFr Xo c T ι), OverLa w T.V ι 1 ∧ algOn Z T ι y' := by
  atlas_forward_decl GlobalTheory.CompletionPoint.exists_intFr_index_one
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.UnramCM

theorem unramPts_of_cm : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (Dw.p = 0 ∨ Dw.q = 0 ∨ (3 ≤ Dw.p + Dw.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → (∀ p : ℕ, p.Prime → l.GoodAt p) → UnramPts Xo c (badPrimes H l) := by
  intro hP E _ _ _ H Dw l Xo c hpq hcase hg
  refine UnramPts.of_index_one fun Z w hw => ?_
  have hch : ∃ q : ℕ, q.Prime ∧ ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal := by
    haveI := w.isMaximal
    haveI : Finite (𝓞 c.F ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
    letI := Ideal.Quotient.field w.asIdeal
    refine ⟨ringChar (𝓞 c.F ⧸ w.asIdeal), CharP.char_is_prime (𝓞 c.F ⧸ w.asIdeal) _, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.Nat.cast_ringChar
  obtain ⟨q, hq, hqw⟩ := hch
  have hqB : q ∉ badPrimes H l := fun h => hw q h hqw
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) l.A_pos.ne'
  have h3 : 3 ≤ l.M' := le_trans l.three_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) (Nat.dvd_lcm_left _ _))
  have hqd : ¬ q ∣ 2 * l.M' * H.d := fun h => hqB <| by
    have hD : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero E)
    have hne : 2 * H.d * (discr E).natAbs * l.M' ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero H.d_prime.ne_zero) hD) hM
    rw [badPrimes, Nat.mem_primeFactors_of_ne_zero hne]
    refine ⟨hq, ?_⟩
    have : 2 * l.M' * H.d ∣ 2 * H.d * (discr E).natAbs * l.M' :=
      ⟨(discr E).natAbs, by ring⟩
    exact h.trans this
  obtain ⟨F', _, hdisc, hcurve⟩ := GlobalTheory.T.exists_field_unramified_curve hP E H l.M' q h3 hq hqd
  let K : IntermediateField ℚ ℂ := c.F ⊔ F'
  haveI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField K := ⟨⟩
  have hle : c.F ≤ K := le_sup_left
  have hK : GlobalTheory.CompRat.CurveOver H K l.M' := fun τ hτ =>
    hcurve τ fun x hx => hτ x (le_sup_right (a := c.F) hx)
  obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.T.compositum_intermediateField_exists_place_valuation_eq c.F F' K hle rfl q hq hdisc w hqw
  letI : Algebra c.F K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_framedPoint_liesOn_component_cmCurve_field E H Dw l Xo c hpq hcase K hle hK Z
  exact GlobalTheory.T.exists_integralFramedPoint_completion_index_one E H Dw l Xo c hpq hg Z K y hy w 𝔭 h𝔭

end GlobalTheory.UnramCM
end
