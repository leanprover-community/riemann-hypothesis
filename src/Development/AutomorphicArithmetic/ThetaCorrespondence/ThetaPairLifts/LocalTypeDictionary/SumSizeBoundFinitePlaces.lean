import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairIntegralRatioOfHyp
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.ImportsAlt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRowOfDictionaryDepthStatement

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem UpperTheory.WildA.ker_wild_ramification_map :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
          (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
          ∀ (ch : Choice R) (CF : ℝ), ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.NormSum.Inp D →
          DictAt ch → ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
          ∀ (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum ch.G t p), 0 < k → IsCosetDatum k d → d.z = 1 →
          d.P = locPl ch.G t → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ch.S.Z.IsRatAt d x y →
          ∀ (w : PlL D) (l : ℕ), l.Prime → (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → Away ch.G t w →
          ∀ (a : ℝ) (v : VV ℂ (wt ch.G p.small)), InLat _ w a (latAt ch.S.toGridChoice p.small x) v →
            InLat _ w (a + (vw w ((l : ℕ) : D.what₂.LL) : ℝ) * C1 *
                GlobalTheory.SumSize.TopInt.kerLoss ch.G δ C1 large₂.sc.b p.small p.big l (padicValNat l k))
              (latAt ch.S.toGridChoice p.big y) (ch.S.Z.kkMap 1 d x y v) := by
  refine ⟨1, one_pos, ?_⟩
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch CF _ _ _ _ hI hDict S δ hL t p hp k d hk hd hz hP x y hR w l hl hw hA a v hv
  have hn := DefPair.nodes hp
  obtain ⟨k', hk', hd', hle, hsp⟩ := UpperTheory.WildA.depth large₂ hS.size d hP w l hl hw hA k hk hd
  obtain ⟨r, U, hU, e, hx⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.small hn.1 l hl x
  obtain ⟨r', U', hU', e', hy⟩ := UpperTheory.WildA.toStd ch.S.toGridChoice p.big hn.2 l hl y
  have hmv := UpperTheory.WildA.move ch.S.Z hS.core.lev t p hp d x r y r' U U' hU hU'
  have hR' : ch.S.Z.IsRatAt d (r * x) (r' * y) := by
    intro i j
    have := UpperTheory.WildA.ratMove D _ _ _ _ _ _ hmv (fun i j => by
      have := hR i j
      rwa [Normal.kkIn, LinearMap.toMatrix_apply] at this) i j
    rwa [Normal.kkIn, LinearMap.toMatrix_apply]
  have h1 := UpperTheory.WildA.kerStd D large₂ Γ Pl0 T A Ks R F hS ch hI hDict S δ hL t p hp k' d hk' hd' hz hP _ _ hR' w l hl hw hsp hx hy
    large₂.sc.b
  have h2 := (UpperTheory.WildA.latMove D _ w a _ U v).2 hv
  rw [← e] at h2
  have h3 := UpperTheory.WildA.matLat D _ _ w l hl hw _ _ hx hy _ _ h1 a _ h2
  have h4 := LinearMap.congr_fun hmv v
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h4
  rw [h4, e'] at h3
  refine GlobalTheory.SumSize.TopInt.inLat_mono ((UpperTheory.WildA.latMove D _ w _ _ U' _).1 h3) ?_
  rw [mul_one]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (GlobalTheory.SumSize.TopInt.kerLoss_mono _ _ _ _ _ _ _ hle)
    (by exact_mod_cast GlobalTheory.SumSize.TopInt.vw_natCast_nonneg w l))
end
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open GlobalTheory.SumSize.TopInt
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → GlobalTheory.SumSize.PairInt.PairIntRatK := by
  intro hP hI hD
  obtain ⟨C1, hC1, hPL⟩ := _root_.UpperTheory.WildA.ker_wild_ramification_map
  obtain ⟨C0, hC0, hS⟩ := UpperTheory.WildA.lossOne C1 hC1
  obtain ⟨CF2, hD⟩ := hD
  refine ⟨CF2, fun CF hCF => ?_⟩
  obtain ⟨C02, hD⟩ := hD CF hCF
  refine ⟨max C0 C02, fun ε C hC => ?_⟩
  obtain ⟨x2, hD⟩ := hD ε C (le_of_max_le_right hC)
  refine ⟨x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hs ch hch hsc hfo => ?_⟩
  have dict : DictAt ch := hD D large₂ he hx Γ Pl0 T A Ks R F hs ch hch hsc hfo
  obtain ⟨S, δ, hL⟩ := (GlobalTheory.NormSum.letters_and_sizes D (hI D).g1).1
  have hgap : ch.sc.cGap = 1 := by
    have e : ch.sc = ⟨1, CF, large₂.sc.b⟩ := hsc
    rw [e]
  obtain ⟨S', h, hE, hh⟩ := hS (G := ch.G) large₂ hs.size hs.host hgap S δ hL
  obtain ⟨l1, l2, l3⟩ := UpperTheory.WildA.expLoss D S' h _ hE
  obtain ⟨-, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs.size
  refine ⟨_, ⟨l1, l2, fun s => (l3 s).trans ?_⟩, ?_⟩
  · have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg (by linarith)
    have hsig : 0 ≤ sig ch.G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
    have hCC : C0 ≤ C := le_of_max_le_left hC
    have h1 : C0 ≤ C * D.R.m := by nlinarith
    have h2 : (0 : ℝ) ≤ D.R.f * (bigN D : ℝ) ^ 2 * (Real.log large₂.sc.b + sig ch.G) * large₂.sc.b := by
      have : (0 : ℝ) ≤ large₂.sc.b := by linarith
      positivity
    have := mul_le_mul_of_nonneg_right h1 h2
    unfold bOne
    linarith
  · intro t p hp w hw k d hk hcos hz hPl hdep x y hr a v hv
    have key := hPL D large₂ Γ Pl0 T A Ks R F hs ch CF hch hsc hfo hP (hI D) dict S δ hL t p hp k d hk hcos hz hPl x y hr
      w (primeUnder w) (primeUnder_prime w) (primeUnder_mem w) hw a v hv
    refine inLat_mono key ?_
    have h1 := kerLoss_mono ch.G δ C1 large₂.sc.b p.small p.big (primeUnder w)
      (hdep _ (primeUnder_prime w) (primeUnder_mem w))
    have h2 := (mul_le_mul_of_nonneg_left h1 hC1.le).trans (hh p hp _ (primeUnder_prime w))
    have h0 : (0 : ℝ) ≤ (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) := by exact_mod_cast vw_natCast_nonneg w _
    have h3 := mul_le_mul_of_nonneg_left h2 h0
    rw [mul_assoc]
    linarith
end
end

section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open GlobalTheory.SumSize
namespace GlobalTheory.SumSize
theorem finite_place_sum_size_bound (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) (hD : DictK) (hd : DepthK) : FinRowK := by
  have hG : PairInt.PairIntRatK := _root_.GlobalTheory.T.pairIntRatK_of_thetaLocalInputs hP hI hD
  obtain ⟨CF0, h⟩ := BigC.and hG hd
  refine ⟨CF0, fun CF hCF => ?_⟩
  obtain ⟨C0, h⟩ := h CF hCF
  refine ⟨C0, fun ε C hC => ?_⟩
  obtain ⟨x0, h⟩ := h ε C hC
  refine ⟨x0, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch h1 h2 h3 => ?_⟩
  obtain ⟨⟨dl, hL, h⟩, hDe⟩ := h D large₂ he hx Γ Pl0 T A Ks R F hS ch h1 h2 h3
  refine ⟨dl, hL, ?_⟩
  intro t w hw Φ β d hO c i a v hv
  obtain ⟨hβ, τ, hτ, hdτ⟩ := hO
  have hrat := (h3.isRatAt hβ hτ hdτ c).2 i
  obtain ⟨hk, ⟨e, -, hPz, -⟩, hcos⟩ := hτ
  have hdep := (hDe t Φ β hβ).2
  exact h t (.chi i D.R.m) ⟨i.2, rfl⟩ w hw _ (d.2 i) hk ((hcos d hdτ).2 i) ((hPz d hdτ).2 i).2.2 ((hPz d hdτ).2 i).1
    (fun l hl hlw => hdep w l hl hlw hw) _ _ hrat a v hv
end GlobalTheory.SumSize
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_size_bound_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → FinRowK := by
  first | exact @_root_.GlobalTheory.SumSize.finite_place_sum_size_bound | exact _root_.GlobalTheory.SumSize.finite_place_sum_size_bound | (intros; apply _root_.GlobalTheory.SumSize.finite_place_sum_size_bound <;> assumption)
end
end
