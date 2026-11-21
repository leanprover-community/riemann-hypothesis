import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsQuotEquiv
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BlockHarmLevOfBlockHarm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ShortSeriesBlockProduct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSimInducing
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ModuliUnivEtaKilled
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaValueNaturalAlgebraMap
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValuesInvariantUniversalEndomorphism
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AlphaFormHarmonicValueAtFramedPoint
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueNormalisedPullbackRationalNorm
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsNormalisedPullbackSectionMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricTranslatesMultiplicationPullbackDescrip
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SumSupportCMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueEqChartValue
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HarmonicValueChainRuleNormalizedPullback
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LatticeTrivialAtPrimeIndicesAndUnits
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortThetaValueFieldEqMapSubfieldData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleExistsAndEval
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmAMemSpanShort
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TotalDegreeLeOfRowDeg

section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem pow_mul_short_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (ka wL : WeightFamilies.Wt D j) (hka : ka.n = D.R.nV)
    (step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      X.emb wL (X.thAll wL) * X.emb w (X.shortTh w) ≤ X.emb (WeightAlgebra.wadd w wL) (X.shortTh (WeightAlgebra.wadd w wL))) :
    ∀ (t : ℕ) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → deg w + t • deg wL = deg ka →
      X.emb wL (X.thAll wL) ^ t * X.emb w (X.shortTh w) ≤ X.emb ka (X.shortTh ka) := by
  intro t
  induction t with
  | zero =>
    intro w _ e
    rw [zero_smul, add_zero] at e
    obtain rfl := deg_inj e
    rw [pow_zero, one_mul]
  | succ t ih =>
    intro w hr e
    have hn : w.n + (t + 1) * wL.n = ka.n := congrArg (fun x : Deg D j => x.2.2) e
    rw [pow_succ, mul_assoc]
    refine le_trans (mul_le_mul' le_rfl (step w hr fun h0 => ?_)) (ih (WeightAlgebra.wadd w wL) (hr.trans (Nat.le_add_right _ _)) ?_)
    · have h1 : (t + 1) * wL.n = 0 := by omega
      exact (Nat.mul_eq_zero.1 h1).resolve_left (Nat.succ_ne_zero t)
    · rw [deg_wadd, ← e, succ_nsmul]
      abel

theorem emb_mul_le {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    {w w' w'' : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {N' : Submodule (𝓞 B.KO) (B.Cusp j w')}
    {N'' : Submodule (𝓞 B.KO) (B.Cusp j w'')}
    (h : ∀ G ∈ N', ∀ F ∈ N, ∃ H ∈ N'', X.inc w'' H = X.inc w' G * X.inc w F) :
    X.emb w N * X.emb w' N' ≤ X.emb w'' N'' := by
  rw [mul_comm, Submodule.mul_le]
  rintro _ ⟨G, hG, rfl⟩ _ ⟨F, hF, rfl⟩
  exact h G hG F hF

theorem mul_mem_span_of_gen {O R : Type} [CommRing O] [CommRing R] [Algebra O R] {s t : Set R} {N : Submodule O R}
    (h : ∀ g ∈ s, ∀ f ∈ t, g * f ∈ N) {x y : R} (hx : x ∈ Submodule.span O s) (hy : y ∈ Submodule.span O t) :
    x * y ∈ N := by
  have hle : Submodule.span O s * Submodule.span O t ≤ N := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨g, hg, f, hf, rfl⟩
    exact h g hg f hf
  exact hle (Submodule.mul_mem_mul hx hy)

theorem productsShort_of_oneFactor (one : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (w wL : WeightFamilies.Wt D j), D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) → ∀ g ∈ T.sh j w, ∀ f ∈ T.th j wL, g * f ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j (WeightAlgebra.wadd w wL))) : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ka.n = D.R.nV → ProductsShort (recPJ h j hj) ka wL wF Tn := by
  intro hC D T h j hj hsh hone hA ka wL wF Tn hF hn hD hr hka
  have step : ∀ w : WeightFamilies.Wt D j, D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) →
      (recPJ h j hj).emb wL ((recPJ h j hj).thAll wL) * (recPJ h j hj).emb w ((recPJ h j hj).shortTh w) ≤
        (recPJ h j hj).emb (WeightAlgebra.wadd w wL) ((recPJ h j hj).shortTh (WeightAlgebra.wadd w wL)) := by
    intro w hw h0
    refine emb_mul_le (recPJ h j hj) fun G hG F hF' => ?_
    have hc : (G.1 : T.R j) * F.1 ∈ cutR T.C j (WeightAlgebra.wadd w wL) := by
      rw [cutR_eq T.C hj]
      exact h.toLawsCore.mul j hj w wL _ (cutR_le T.C j w G.2) _ (cutR_le T.C j wL F.2)
    refine ⟨⟨_, hc⟩, ?_, ?_⟩
    · exact mul_mem_span_of_gen (one hC D T h j hj hsh hone hA w wL hw h0) hG hF'
    · exact (incG_mul deg (cutR T.C j) (deg_wadd w wL) G F _).symm
  have key := pow_mul_short_le (recPJ h j hj) ka wL hka step
  have hdeg : deg wF + Tn • deg wL = deg ka := by
    obtain ⟨_, hP, hM⟩ := hF
    refine Prod.ext (funext fun τ => funext fun i => ?_) (Prod.ext (funext fun τ => funext fun i => ?_) hn.symm)
    · change wF.aP τ i + Tn * wL.aP τ i = ka.aP τ i
      have := hP τ i
      zify
      linarith
    · change wF.aM τ i + Tn * wL.aM τ i = ka.aM τ i
      have := hM τ i
      zify
      linarith
  refine sup_le (sup_le (key Tn wF hr hdeg) (key _ _ (hr.trans (Nat.le_add_right _ _)) ?_)) le_rfl
  have e : deg ((recPJ h j hj).wF0 wL wF) = deg wF + WeightFamilies.dimY D j • deg wL := rfl
  rw [e, add_assoc, ← add_nsmul, Nat.add_sub_of_le hD, hdeg]

end GlobalTheory.FormTies
end

section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FormTies
open scoped Classical

namespace GlobalTheory.MoreColumns

open GlobalTheory.DatumInverseCharacter

theorem sum_append {A F : Type} [Fintype A] [CommRing F] {n m : ℕ} (f : (Fin n → A) → F) (χ : Fin (n + m) → A → F) :
    ∑ x : Fin (n + m) → A, f (fun b => x (Fin.castAdd m b)) * ∏ b, χ b (x b) =
      (∑ y : Fin n → A, f y * ∏ b, χ (Fin.castAdd m b) (y b)) * ∏ b : Fin m, ∑ a, χ (Fin.natAdd n b) a := by
  rw [← (Fin.appendEquiv n m).sum_comp, Fintype.sum_prod_type, Finset.prod_univ_sum, Fintype.piFinset_univ,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.prod_univ_add]
  simp [mul_assoc]

theorem zpow_sum {F ι : Type} [Field F] {z : F} (hz : z ≠ 0) (s : Finset ι) (a : ι → ℤ) :
    z ^ (∑ i ∈ s, a i) = ∏ i ∈ s, z ^ a i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ hz, ih]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem char_sum (D : Datum H) {N : ℕ} (hN : 0 < N) {I : Ideal (𝓞 E)}
    (hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(N : 𝓞 E)})
    (hI : I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) {F : Type} [Field F] {z : F} (hz : IsPrimitiveRoot z N)
    [Fintype (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))] (v : D.La) :
    ∑ x : D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La), z ^ D.EF (qRep x) (cHalf H I • v) =
      if v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) then
        (Nat.card (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) : F) else 0 := by
  obtain ⟨hc, hc1⟩ := HalfPairing.cHalf_spec I hI
  have hz0 : z ≠ 0 := hz.ne_zero hN.ne'
  have hmk : ∀ u : D.La, z ^ D.EF (qRep (Submodule.Quotient.mk u :
      D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La))) (cHalf H I • v) =
      z ^ D.EF u (cHalf H I • v) := by
    intro u
    refine zpow_congr hN hz.pow_eq_one ?_
    rw [← LinearMap.sub_apply, ← map_sub]
    exact dvd_left D hp hc v ((Submodule.Quotient.eq _).1 (qRep_spec _))
  let χ : AddChar (D.La ⧸ (I.map (H.bar : 𝓞 E →+* 𝓞 E) • ⊤ : Submodule (𝓞 E) D.La)) F :=
    { toFun := fun x => z ^ D.EF (qRep x) (cHalf H I • v)
      map_zero_eq_one' := by
        have := hmk 0
        rw [map_zero, LinearMap.zero_apply, zpow_zero] at this
        exact this
      map_add_eq_mul' := fun x y => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        rw [← Submodule.Quotient.mk_add, hmk, hmk, hmk, map_add, LinearMap.add_apply, zpow_add₀ hz0] }
  have hiff : χ = 0 ↔ v ∈ (I • ⊤ : Submodule (𝓞 E) D.La) := by
    constructor
    · intro h
      have h1 : ∀ y, (N : ℤ) ∣ D.EF (cHalf H I • v) y := fun y => by
        have h2 : χ (Submodule.Quotient.mk y) = 1 := by rw [h]; rfl
        have h3 : z ^ D.EF y (cHalf H I • v) = 1 := (hmk y).symm.trans h2
        rw [HalfPairing.ef_swap, dvd_neg]
        exact (hz.zpow_eq_one_iff_dvd _).1 h3
      have hNI : (N : 𝓞 E) ∈ I := by
        have : Ideal.span {(N : 𝓞 E)} ≤ I := hp ▸ (Ideal.mul_le_inf.trans inf_le_left)
        exact this (Ideal.subset_span rfl)
      have h4 := mem_of_modN D hNI (modN_of_dvd D hN h1)
      have : v = cHalf H I • v - (cHalf H I - 1) • v := by rw [sub_smul, one_smul, sub_sub_cancel]
      rw [this]
      exact sub_mem h4 (Submodule.smul_mem_smul hc1 trivial)
    · intro h
      ext x
      exact (hz.zpow_eq_one_iff_dvd _).2 (dvd_right D hp hc _ h)
  have := AddChar.sum_eq_ite χ
  rw [Nat.card_eq_fintype_card]
  simp only [← hiff]
  convert this using 2
  rfl

theorem coeff_more_columns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n m : ℕ) (d : DeltaDat Xo c n) (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F), d.IsLev → Dw.p + Dw.q ≤ n → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d) (ph' : (Fin (n + m) → LaJ Xo c d) → c.F) (x₀' : Fin (n + m) → LaJ Xo c d), d.PhiPin ph ψ x₀ → (withCoeff d φ').PhiPin ph' ψ x₀' → ∃ ζ : c.F, IsOfFinOrder ζ ∧ ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) * (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (LaI Xo c d) : c.F) ^ m else 0) := by
  intro E _ _ _ H Dw l Xo c n m d φ' hd hn ψ ph x₀ ph' x₀' hpin hpin'
  obtain ⟨-, huniq, adj, -, hadj⟩ := HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨-, hM, -, hMb, hI, -⟩ := hd
  obtain ⟨ha, hb, hc, hone, hspan, hφ⟩ := hpin
  obtain ⟨ha', hb', hc', hone', hspan', hφ'⟩ := hpin'
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hMb
  have hI0 : d.I ≠ ⊥ := by
    intro h
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  have hJ0 : d.I.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hIJ
    exact hpd.ne' (by exact_mod_cast hIJ)
  haveI : Finite (𝓞 E ⧸ d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hJ0
  haveI : Finite (𝓞 E ⧸ d.I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI0
  haveI := Dw.fin
  haveI := Dw.proj
  obtain ⟨e⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) (d.I.map (H.bar : 𝓞 E →+* 𝓞 E)) _ Dw.rank
  obtain ⟨e'⟩ := HalfPairing.nonempty_equiv_quot (N := Dw.La) d.I _ Dw.rank
  haveI : Finite (LaJ Xo c d) := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (LaI Xo c d) := Finite.of_equiv _ e'.toEquiv.symm
  haveI : Finite (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) :=
    Finite.of_injective (fun k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d => (k : LaI Xo c d → LaI Xo c d))
      DFunLike.coe_injective
  have hcard : Nat.card (LaJ Xo c d) = Nat.card (LaI Xo c d) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, Nat.card_fun, Nat.card_fun,
      Nat.card_congr (Ideal.quotientEquiv d.I _ (H.bar : 𝓞 E ≃+* 𝓞 E) rfl).toEquiv]
  have himg : ∀ {k : ℕ} (hk : Dw.p + Dw.q ≤ k) (x : Fin k → LaJ Xo c d),
      x '' {b | b.val < Dw.p + Dw.q} = Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hk b)) := by
    intro k hk x
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hk b, b.2, rfl⟩
  have hn' : Dw.p + Dw.q ≤ n + m := hn.trans (Nat.le_add_right _ _)
  have hs₀ := (congrArg (Submodule.span (𝓞 E)) (himg hn x₀)).symm.trans hspan
  have hspan₁ : Submodule.span (𝓞 E) (x₀' '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hspan'
  have hb₁ : ∀ x, ph' x ≠ 0 → Submodule.span (𝓞 E) (x '' {b | b.val < Dw.p + Dw.q}) = ⊤ := hb'
  have hs₀' := (congrArg (Submodule.span (𝓞 E)) (himg hn' x₀')).symm.trans hspan₁
  obtain ⟨g, hg, -⟩ := huniq _ _ hs₀ hs₀'
  have hy₀ : ph (fun b => x₀' (Fin.castAdd m b)) = (((ψ (adj g))⁻¹ : c.Fˣ) : c.F) := by
    have h1 := hc (adj g) g ((hadj _ _).2 rfl) x₀
    rw [hone, mul_one] at h1
    rw [← h1]
    exact ha _ _ fun b hb => (hg ⟨b.1, hb⟩).symm
  have hph : ∀ x : Fin (n + m) → LaJ Xo c d,
      ph' x = ((ψ (adj g) : c.Fˣ) : c.F) * ph (fun b => x (Fin.castAdd m b)) := by
    intro x
    by_cases hx : Submodule.span (𝓞 E) (Set.range (fun b : Fin (Dw.p + Dw.q) => x (Fin.castLE hn' b))) = ⊤
    · obtain ⟨g', hg', -⟩ := huniq _ _ hs₀' hx
      have h1 : ph' (fun b => g' (x₀' b)) = (((ψ (adj g'))⁻¹ : c.Fˣ) : c.F) * ph' x₀' :=
        hc' (adj g') g' ((hadj _ _).2 rfl) x₀'
      have h2 := hc (adj g') g' ((hadj _ _).2 rfl) (fun b => x₀' (Fin.castAdd m b))
      have h3 : ph' x = ph' (fun b => g' (x₀' b)) := ha' _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      have h4 : ph (fun b => x (Fin.castAdd m b)) = ph (fun b => g' (x₀' (Fin.castAdd m b))) :=
        ha _ _ fun b hb => (hg' ⟨b.1, hb⟩).symm
      rw [h3, h4, h1, h2, hy₀, hone', mul_one, mul_left_comm, Units.mul_inv, mul_one]
    · have h1 : ph' x = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn' x)).symm.trans (hb₁ x h))
      have h2 : ph (fun b => x (Fin.castAdd m b)) = 0 := by
        by_contra h
        exact hx ((congrArg (Submodule.span (𝓞 E)) (himg hn _)).symm.trans (hb _ h))
      rw [h1, h2, mul_zero]
  refine ⟨((ψ (adj g) : c.Fˣ) : c.F),
    (Units.coeHom c.F).isOfFinOrder (ψ.isOfFinOrder (isOfFinOrder_of_finite _)), fun q => ?_⟩
  set z : d.c₂.F := (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd) with hzdef
  have hz : IsPrimitiveRoot z d.pd := by
    have h1 : d.pd ∣ d.l₂.M' := (hM ▸ Dvd.intro_left _ rfl : d.pd ∣ d.l₂.M).trans (Nat.dvd_lcm_left _ _)
    have h2 : 0 < d.l₂.M' := Nat.lcm_pos hM₂ d.l₂.A_pos
    have h0 : IsPrimitiveRoot (zeta d.l₂.M') d.l₂.M' := Complex.isPrimitiveRoot_exp _ h2.ne'
    have h3 : IsPrimitiveRoot (⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) d.l₂.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap d.c₂.F ℂ) h0 (algebraMap d.c₂.F ℂ).injective
    exact h3.pow h2 (Nat.div_mul_cancel h1).symm
  have hz0 : z ≠ 0 := hz.ne_zero hpd.ne'
  haveI := Fintype.ofFinite (LaJ Xo c d)
  have h1 : d.eF (φ' q) = ∑ᶠ x : Fin (n + m) → LaJ Xo c d, d.eF (ph' x) *
      z ^ (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b))) := hφ' q
  apply d.eF.injective
  rw [h1, map_mul, map_mul, hφ, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [zpow_sum hz0, hph, map_mul, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_append (fun y => d.eF (ph y)) (fun b a => z ^ Dw.EF (qRep a) (cHalf H d.I • levRep (q b)))]
  congr 1
  simp only [char_sum Dw hpd hIJ hI hz]
  rw [Finset.prod_ite_zero]
  simp only [Finset.mem_univ, forall_true_left, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  split_ifs
  · rw [map_pow, map_natCast, ← hcard]
  · rw [map_zero]

end GlobalTheory.MoreColumns
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BetaOfSum

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BetaEx GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility GlobalTheory.ShortLawsCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}

theorem mem_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (v : Fin (n₁ + n₂) → E) : v ∈ (blockLat ⟨M₁⟩ ⟨M₂⟩).La ↔
      (fun i => v (Fin.castAdd n₂ i)) ∈ M₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ M₂ := Iff.rfl

omit [NumberField E] in

theorem det_block (u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h : ∀ i j, u (Fin.castAdd n₂ i) (Fin.natAdd n₁ j) = 0) :
    u.det = (Matrix.of fun i j => u (Fin.castAdd n₂ i) (Fin.castAdd n₂ j)).det *
      (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.natAdd n₁ j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₁₂ _
    (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.castAdd n₂ j))]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [h]

omit [NumberField E] in

theorem det_pure_mem (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (w : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h₁ : ∀ i, (fun j => w i (Fin.castAdd n₂ j)) ∈ M₁) (h₂ : ∀ i, (fun j => w i (Fin.natAdd n₁ j)) ∈ M₂)
    (h : ∀ i, (∀ j, w i (Fin.castAdd n₂ j) = 0) ∨ ∀ j, w i (Fin.natAdd n₁ j) = 0) :
    w.det ∈ detSpan M₁ * detSpan M₂ := by
  by_cases h0 : w.det = 0
  · rw [h0]; exact zero_mem _
  have h0' := h0
  rw [Matrix.det_apply] at h0'
  obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0'
  have hd : ∀ i, w (σ i) i ≠ 0 := fun i hi => hσ (by
    rw [Finset.prod_eq_zero (f := fun k => w (σ k) k) (Finset.mem_univ i) hi, smul_zero])
  have hm : (w.submatrix σ id).det ∈ detSpan M₁ * detSpan M₂ := by
    rw [det_block _ (fun i j => ((h (σ (Fin.castAdd n₂ i))).resolve_left fun g => hd _ (g i)) j)]
    exact Submodule.mul_mem_mul (det_mem _ fun i => h₁ _) (det_mem _ fun i => h₂ _)
  rw [Matrix.det_permute] at hm
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> rw [e] at hm
  · simpa using hm
  · simpa using hm

theorem detSpan_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) :
    detSpan (blockLat ⟨M₁⟩ ⟨M₂⟩).La = detSpan M₁ * detSpan M₂ := by
  classical
  have z₁ : (fun _ => 0) ∈ M₁ := M₁.zero_mem
  have z₂ : (fun _ => 0) ∈ M₂ := M₂.zero_mem
  apply le_antisymm
  · refine Submodule.span_le.2 fun d hd => ?_
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ d).1 hd
    let a : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append (fun j => v i (Fin.castAdd n₂ j)) 0
    let b : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E := fun i => Fin.append 0 (fun j => v i (Fin.natAdd n₁ j))
    have e : (v : Fin (n₁ + n₂) → Fin (n₁ + n₂) → E) = a + b := by
      funext i j
      induction j using Fin.addCases <;> simp [a, b]
    have e2 : v.det = ∑ s : Finset (Fin (n₁ + n₂)), (Matrix.of (s.piecewise a b)).det := by
      have := (Matrix.detRowAlternating (n := Fin (n₁ + n₂)) (R := E)).toMultilinearMap.map_add_univ a b
      rw [← e] at this
      exact this
    rw [SetLike.mem_coe, e2]
    refine Submodule.sum_mem _ fun s _ => det_pure_mem M₁ M₂ _ (fun i => ?_) (fun i => ?_) (fun i => ?_)
    · by_cases hi : i ∈ s
      · simpa [hi, a] using ((mem_block _ _ _).1 (hv i)).1
      · simpa [hi, b] using z₁
    · by_cases hi : i ∈ s
      · simpa [hi, a] using z₂
      · simpa [hi, b] using ((mem_block _ _ _).1 (hv i)).2
    · by_cases hi : i ∈ s
      · exact Or.inr fun j => by simp [hi, a]
      · exact Or.inl fun j => by simp [hi, b]
  · rw [detSpan, detSpan, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨v, hv, rfl⟩ := (mem_detSet _ _).1 hx
    obtain ⟨w, hw, rfl⟩ := (mem_detSet _ _).1 hy
    let u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E :=
      Matrix.of (Fin.append (fun i => Fin.append (v i) 0) (fun i => Fin.append 0 (w i)))
    have e : u.det = v.det * w.det := by
      rw [det_block u (fun i j => by simp [u])]
      congr 2 <;> ext i j <;> simp [u]
    change v.det * w.det ∈ detSpan _
    rw [← e]
    refine det_mem _ fun i => (mem_block _ _ _).2 ?_
    induction i using Fin.addCases with
    | left i => exact ⟨by simpa [u] using hv i, by simpa [u] using z₂⟩
    | right i => exact ⟨by simpa [u] using z₁, by simpa [u] using hw i⟩

theorem block_Ln (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    (blockLat Λ₁ Λ₂).Ln = (blockLat ⟨Λ₁.Ln⟩ ⟨Λ₂.Ln⟩).La := by
  ext v
  change (v ∈ (blockLat Λ₁ Λ₂).La ∧ v ∈ stdLat E _) ↔ _
  rw [mem_std_block, mem_block, mem_block]
  exact and_and_and_comm

theorem index_block (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    ((blockLat Λ₁ Λ₂).Ln.toAddSubgroup.addSubgroupOf (blockLat Λ₁ Λ₂).La.toAddSubgroup).index =
      (Λ₁.Ln.toAddSubgroup.addSubgroupOf Λ₁.La.toAddSubgroup).index *
        (Λ₂.Ln.toAddSubgroup.addSubgroupOf Λ₂.La.toAddSubgroup).index := by
  let φ : (blockLat Λ₁ Λ₂).La.toAddSubgroup →+ Λ₁.La.toAddSubgroup × Λ₂.La.toAddSubgroup :=
    { toFun := fun v => (⟨fun i => v.1 (Fin.castAdd n₂ i), v.2.1⟩, ⟨fun j => v.1 (Fin.natAdd n₁ j), v.2.2⟩)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨Fin.append x y, (mem_block _ _ _).2 ⟨by simpa using hx, by simpa using hy⟩⟩, ?_⟩
    ext j <;> simp [φ]
  rw [← AddSubgroup.index_prod, ← AddSubgroup.index_comap_of_surjective _ hφ, block_Ln]
  rfl

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n₁ n₂ : ℕ}

theorem idealAt_block (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) (τ : E →+* ℂ) :
    idealAt c (blockLat ⟨M₁⟩ ⟨M₂⟩).La τ = idealAt c M₁ τ * idealAt c M₂ τ := by
  have e := detSpan_block M₁ M₂
  unfold detSpan at e
  unfold idealAt
  rw [← span_image_span, e, Submodule.span_mul_span, span_image_span, Submodule.span_mul_span, Set.image_mul]

theorem isBeta_block {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {β₁ β₂ : c.F} (b₁ : IsBeta Dw c Λ₁ β₁)
    (b₂ : IsBeta Dw c Λ₂ β₂) : IsBeta Dw c (blockLat Λ₁ Λ₂) (β₁ * β₂) := by
  refine ⟨mul_ne_zero b₁.1 b₂.1, ?_, fun σ => ?_⟩
  · have e₁ := b₁.2.1
    have e₂ := b₂.2.1
    unfold BetaIs at e₁ e₂ ⊢
    rw [block_Ln]
    simp only [idealAt_block c Λ₁.La Λ₂.La, idealAt_block c Λ₁.Ln Λ₂.Ln, mul_pow, Finset.prod_mul_distrib]
    rw [← e₁, ← e₂, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span, mul_mul_mul_comm]
  · rw [index_block, map_mul, norm_mul, mul_pow, b₁.2.2 σ, b₂.2.2 σ, Nat.cast_mul, mul_pow]

theorem isBeta_unit_block (n₁ : ℕ) (Λ₂ : GenLat E n₂) (β : c.F) :
    IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β := by
  have e : (unitLat E n₁).Ln = (unitLat E n₁).La := inf_idem _
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c (unitLat E n₁).La τ ^ Dw.mult τ) :=
    IsUnit.prod_univ_iff.2 fun τ =>
      (isUnit_idealAt c (trivAt_std n₁ 0) (unimod_std n₁) zero_ne_one τ).pow _
  refine and_congr_right fun _ => and_congr ?_ (forall_congr' fun σ => ?_)
  · unfold BetaIs
    rw [block_Ln, e]
    simp only [idealAt_block c (unitLat E n₁).La Λ₂.La, idealAt_block c (unitLat E n₁).La Λ₂.Ln, mul_pow,
      Finset.prod_mul_distrib]
    rw [mul_left_comm, hu.mul_right_inj]
  · rw [index_block, e]
    simp

theorem blockBeta : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (bad : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.BlockBeta Dw c bad := by
  intro E _ _ _ H Dw l c bad
  refine ⟨fun n₁ n₂ Λ₁ Λ₂ h₁ h₂ β₁ β₂ β b₁ b₂ => ⟨fun b => ?_, ?_⟩,
    fun n₁ n₂ Λ₂ _ => ⟨GlobalTheory.Survey.BaseClassMove.isBeta_unit c n₁, isBeta_unit_block c n₁ Λ₂⟩⟩
  · have hB := latOK_block h₁ h₂
    exact isBeta_ratio c hB.1 hB.2.2 (isBeta_block c b₁ b₂) b
  · rintro ⟨ζ, hζ, rfl⟩
    exact isBeta_mul c (isBeta_block c b₁ b₂) hζ

end GlobalTheory.BetaOfSum
end
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.StdCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l l₂ : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂}

section Chart

open GlobalTheory.ChartPush

set_option maxHeartbeats 800000 in

theorem hv_push [StarRing (𝓞 E)] {nab : NabV Xo c} {nab₂ : NabV Xo₂ c₂} (hn : IsNab Xo c nab)
    (hn₂ : IsNab Xo₂ c₂ nab₂) {ρ : Xo₂.X ⟶ Xo.X} (ν : SABMap Xo₂.univ.t Xo.univ.t ρ) {S : Type} [Field S]
    [Algebra c.F S] [Algebra c₂.F S] {y : FrPt Xo c S} {y₂ : FrPt Xo₂ c₂ S} {pm : Gx y₂.x ⟶ Gx y.x}
    {w : LB.Iso Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull ν.cm.F)} (h0 : y₂.x ≫ ρ = y.x)
    (p₁ : pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y₂.x) Xo₂.univ.t.G).left)
    (p₂ : pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y₂.x) Xo₂.univ.t.G).left ≫ ν.φ)
    (hw : w.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit.{1}) (fun _ => eSec Xo₂.univ.t.G) (fun _ => 1)) Xo₂.univ.t.PP.rig
      (ν.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig))
    (hu : ∀ τ i, y₂.u τ i ≫ ν.φ = y.u τ i) (f : c.F →+* c₂.F)
    (hf : ∀ a, algebraMap c₂.F S (f a) = algebraMap c.F S a) {n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ HH c a n) (k : ℕ) (b : ℤ) (hb : b = k)
    (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L b (ptO Xo y.x)))
    (F₂ : Fin n → LB.Sec (LPow Xo₂.univ.t.G Xo₂.univ.t.PP.L b (ptO Xo₂ y₂.x)))
    (hF : ∀ i, TranslMove.SecRel (T := ptO Xo₂ y₂.x) (T₀ := ptO Xo y.x) w pm (F i) (F₂ i)) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ i, nab y b (F i) (colOf m i) =
      ∑ m ∈ (MvPolynomial.map f P).support, algebraMap c₂.F S ((MvPolynomial.map f P).coeff m) *
        ∏ i, nab₂ y₂ b (F₂ i) (colOf m i) := by
  subst hb
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨w', hw', hr', hcub⟩ := ν.lin
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol Xo₂) Xo.univ.t.PP.isLB ν.φ w w' hw hw' _ _ hr hr'
  obtain ⟨C, hex, hpin⟩ := hn₂.2 S y₂
  obtain ⟨C', -, -⟩ := hn.2 S y
  choose g hg using fun i => hex k (F₂ i)
  have hA := isAbelianScheme_univ Xo₂
  have hc := (isChart_iff y₂ C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  have hfr := (isFrame_iff y₂ C.d C.x _ _ _ _ _ _ C.e).1 C.frame
  have hP₂ := (isPrim_iff C.wP).1 C.prim
  have hP₁ := (isPrim_iff C'.wP).1 C'.prim
  have hc₁ := isChart_push (ν := ν) h0 hc
  have hx : ∀ m, (C.x m).left ≫ ν.φ = (pu ν h0 _ (C.x m)).left := fun _ => rfl
  obtain ⟨e, he₀, he⟩ := exists_frRel (x := fun m => pu ν h0 _ (C.x m)) hw hx C.e hfr.gen
  have g₁ := isFrame_push hG hA hw hcub hc hx he he₀ (const_ad C.B) hfr
  have r₀ : LB.Gen.Corr Xo₂.univ.t.PP.L _ _ _ _ (LB.pullGen Xo₂.univ.t.PP.L _ _
      (eLG Xo₂.univ.t y₂.x C.d C.x C.B.A.act C.e C.wP 0)
        (homAt y₂.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
      (rigT Xo₂.univ.t.G Xo₂.univ.t.PP.L Xo₂.univ.t.PP.rig (overAt y₂.x S) 1) := C.rig0
  have g₂ := rig_push hG hA hw h0 hr hP₁ hP₂ hc hx he r₀
  have e₁ : (fun ℓ : Lt1 Dw => y.u ℓ.1 ℓ.2) = fun ℓ => y₂.u ℓ.1 ℓ.2 ≫ ν.φ := funext fun ℓ => (hu _ _).symm
  have h₁ : IsChart y C.d C.B.G.F C.B.A.act C.uvec (fun m => pu ν h0 _ (C.x m)) := by
    refine (isChart_iff y C.d _ _ _ _).2 ?_
    rw [e₁]
    exact hc₁
  let C₁ : ChartAt Xo c y := ⟨C.d, C.B, C.uvec, fun m => pu ν h0 _ (C.x m), e, C'.wP, C.h, h₁,
    (isFrame_iff y C.d _ _ _ _ _ _ _ e).2 g₁, C'.prim, C.gauge, g₂⟩
  have hg₁ : ∀ i, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F i) (g i) := fun i =>
    (isGerm_iff y C.d _ _ e _ k (F i) (g i)).2 (isGerm_push hG hA hw hr hP₁ hP₂ hc hc₁ hx he he₀ p₁ p₂
      (fun Z r z J J' hJ hJ' => (hF i Z r z J J' hJ hJ').trans (by rw [zpow_natCast]; rfl))
      ((isGerm_iff y₂ C.d _ _ _ _ k (F₂ i) (g i)).1 (hg i)))
  refine (GlobalTheory.PlaceInt.hv_eq_chartVal E H Dw l Xo c hn.1 nab hn S y C₁ k n F g hg₁ a P hP).trans ?_
  rw [MvPolynomial.support_map_of_injective P f.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, hf]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => (hpin k (F₂ i) (g i) (hg i) (colOf m i)).symm)

end Chart

theorem comp_act_natCast {T : Over Xo.X} (t : T ⟶ Xo.univ.t.G) (n : ℕ) :
    t ≫ Xo.univ.t.act.act (n : 𝓞 E) = t ^ n := by
  rw [TwoLifts.act_natCast_eq, mulA, MonObj.comp_pow, Category.comp_id]

theorem natCast_mul_bar (H : Host E) (n : ℕ) : (n : 𝓞 E) * H.bar (n : 𝓞 E) = ((n ^ 2 : ℕ) : 𝓞 E) := by
  rw [map_natCast, Nat.cast_pow, sq]

theorem pulls_of_uu {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {M κ : ℕ} (hN : Odd (M * κ)) (s : SecN Xo x 1)
    {z t : ptO Xo x ⟶ Xo.univ.t.G} (hz : z ^ (M * κ) = 1) (ht : t ^ (M * κ) ^ 2 = 1) (ht' : (t ^ κ) ^ M ^ 2 = 1)
    {F G} (hF : IsUUOver Xo.univ.t.G Xo.univ.t.PP (M * κ) s z t F)
    (hG : IsUUOver Xo.univ.t.G Xo.univ.t.PP M s 1 (t ^ κ) G) :
    Pulls Xo (κ : 𝓞 E) (sqN Xo M G) (sqN Xo (M * κ) F) := by
  have hM : Odd M := (Nat.odd_mul.1 hN).1
  have hz2 : z ^ (M * κ) ^ 2 = 1 := by rw [sq, pow_mul, hz, one_pow]
  obtain ⟨F₀, F₁, a₁, a₂, a₃⟩ := ((uu_through_moves E H Dw l Xo S x _ hN s).1 z t F hz2 ht).1 hF
  obtain ⟨G₀, G₁, b₁, b₂, b₃⟩ := ((uu_through_moves E H Dw l Xo S x _ hM s).1 1 _ G (one_pow _) ht').1 hG
  have mv := fun (k : ℕ) (hk : Odd k) => GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk
  obtain rfl : G₁ = G₀ := (mv _ hM.pow 1 (one_pow _) G₀).1.unique b₂ (mv _ hM.pow 1 (one_pow _) G₀).2
  have a₄ : Moves Xo z F₀ F₀ := moves_of_pulls E H Dw l Xo S x ((M * κ : ℕ) : 𝓞 E) ((M * κ) ^ 2) 1 _
    (natCast_mul_bar H _) (_root_.one_mul _).symm hN.pow 1 z ((comp_act_natCast z _).trans hz) hz2 s s F₀ F₀
    (mv 1 odd_one 1 (one_pow _) s).2 a₁ a₁
  obtain rfl : F₁ = F₀ := (mv _ hN.pow z hz2 F₀).1.unique a₂ a₄
  have pl := fun F => GlobalTheory.existsUnique_pulls E H Dw l Xo S x (κ : 𝓞 E) (κ ^ 2) (M ^ 2) ((M * κ) ^ 2)
    (natCast_mul_bar H _) (mul_pow _ _ _) F
  obtain ⟨A, hA, -⟩ := pl G₁
  obtain ⟨B, hB, -⟩ := pl (sqN Xo M G)
  have hA' := GlobalTheory.PullComp.pulls_mul E H Dw l Xo S x _ _ _ _ _ s G₁ A b₁ hA
  rw [← Nat.cast_mul] at hA'
  obtain rfl : A = F₁ := (GlobalTheory.existsUnique_pulls E H Dw l Xo S x _ ((M * κ) ^ 2) 1 ((M * κ) ^ 2)
    (natCast_mul_bar H _) (_root_.one_mul _).symm s).unique hA' a₁
  have hm := moves_of_pulls E H Dw l Xo S x (κ : 𝓞 E) (κ ^ 2) (M ^ 2) _ (natCast_mul_bar H _) (mul_pow _ _ _) hN.pow
    _ t (comp_act_natCast t κ) ht _ _ A B b₃ hA hB
  rwa [(mv _ hN.pow t ht A).1.unique a₃ hm]

theorem exists_vt_of {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (N : ℕ) {T : Over X}
    (s : LB.Sec (LPow A L.L 1 T)) (t : T ⟶ A) (k : ℤ) (h : (N : ℤ) ^ 2 = k) (F₀ F₁ : LB.Sec (LPow A L.L k T))
    (h₀ : IsNormPull A L (mulA A N) k 1 s F₀) (U : ThetaGrp A L.L k T) (hU : SymLift A L.L k (N ^ 2) t U)
    (h₁ : IsActOf A L.L k U F₀ F₁) : ∃ F, IsVtOver A L N (· = t) s (t ^ N) F := by
  subst h
  obtain ⟨α₀, α, a1, a2, a3, a4⟩ := (TwoLifts.normPull_iff A L N s F₀).1 h₀
  exact ⟨F₁, t, α₀, α, F₀, U, rfl, rfl, a1, a2, a3, a4, hU, h₁⟩

theorem exists_vt {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {M : ℕ} (hM : Odd M) (s : SecN Xo x 1)
    {t : ptO Xo x ⟶ Xo.univ.t.G} (ht : t ^ M ^ 2 = 1) :
    ∃ F, IsVtOver Xo.univ.t.G Xo.univ.t.PP M (· = t) s (t ^ M) F := by
  obtain ⟨F₀, h₀, -⟩ := GlobalTheory.existsUnique_pulls E H Dw l Xo S x _ (M ^ 2) 1 (M ^ 2)
    (natCast_mul_bar H M) (_root_.one_mul _).symm s
  obtain ⟨F₁, ⟨-, U, hU, h₁⟩, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x _ hM.pow t ht F₀).1
  unfold Pulls at h₀
  rw [TwoLifts.act_natCast_eq] at h₀
  exact exists_vt_of _ _ M s t _ (Nat.cast_pow M 2).symm F₀ F₁ h₀ U hU h₁

theorem killedBy_sq {T : Over Xo.X} {t : T ⟶ Xo.univ.t.G} (h₁ : KilledBy Xo l.Mb (t ^ l.M)) {J : Ideal (𝓞 E)}
    (hJ : J ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤) (h₂ : KilledBy Xo J t) : KilledBy Xo (l.Mb ^ 2) t := by
  let K : Ideal (𝓞 E) :=
    { carrier := {a | t ≫ Xo.univ.t.act.act a = 1}
      add_mem' := fun {a b} ha hb => by
        show t ≫ _ = 1
        rw [Xo.univ.t.act.add, MonObj.comp_mul, show t ≫ _ = 1 from ha, show t ≫ _ = 1 from hb, _root_.mul_one]
      zero_mem' := by
        show t ≫ _ = 1
        rw [← Nat.cast_zero, comp_act_natCast, pow_zero]
      smul_mem' := fun r a ha => by
        have := Xo.univ.t.act.hom r
        show t ≫ _ = 1
        rw [smul_eq_mul, mul_comm, Xo.univ.t.act.mul, ← Category.assoc, show t ≫ _ = 1 from ha, MonObj.one_comp] }
  have k₁ : Ideal.span {(l.M : 𝓞 E)} * l.Mb ≤ K := Ideal.span_singleton_mul_le_iff.2 fun a ha => by
    show t ≫ _ = 1
    rw [Xo.univ.t.act.mul, ← Category.assoc, comp_act_natCast, h₁ a ha]
  have k₂ : J ≤ K := h₂
  show l.Mb ^ 2 ≤ K
  rw [← Ideal.mul_top (l.Mb ^ 2), ← hJ, Ideal.mul_sup]
  refine sup_le (Ideal.mul_le_right.trans k₂) (le_of_eq_of_le ?_ k₁)
  rw [← l.prod, sq, mul_right_comm]

theorem pow_eq_one_of_inZh {m N : ℕ} {T : Over Xo.X} {z : Fin m → (T ⟶ Xo.univ.t.G)}
    (hz : InZh Xo (⟨stdLat E m⟩ : GenLat E m) N z) (b : Fin m) : z b ^ N = 1 := by
  have h := hz.2 1 (fun v hv => by rwa [Matrix.one_mulVec]) (fun i j => if i = j then (N : 𝓞 E) else 0)
    (fun i j => by by_cases e : i = j <;> simp [Matrix.one_apply, e]) b
  rw [List.prod_ofFn, Finset.prod_eq_single b (fun j _ hj => by
    rw [if_neg hj.symm, ← Nat.cast_zero, comp_act_natCast, pow_zero]) (by simp), if_pos rfl, comp_act_natCast] at h
  exact h

section Cover

variable {n : ℕ} (d : DeltaDat Xo c n)

theorem levPt_push (hd : d.IsLev) {S : Type} [CommRing S] {x₂ : Sp S ⟶ d.Xo₂.X} {x₀ : Sp S ⟶ Xo.X}
    (h0 : x₂ ≫ d.r = x₀) (e : (ptO d.Xo₂ x₂ ⟶ d.Xo₂.univ.t.G) →* (ptO Xo x₀ ⟶ Xo.univ.t.G))
    (he : ∀ u, (e u).left = u.left ≫ d.m.φ) {q x : Dw.La} (hq : q ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La))
    (hx : q - (d.pd : 𝓞 E) • x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) :
    levPt d.Xo₂ x₂ q ^ l.M = 1 ∧ e (levPt d.Xo₂ x₂ q) = levPt Xo x₀ x := by
  obtain ⟨-, -, hcop, hMb, -, ⟨heta, -⟩, -⟩ := hd
  have h₁ : levPt d.Xo₂ x₂ q ^ l.M = 1 := by
    rw [levPt, ← MonObj.comp_pow, ← LevelPoints.eta_nsmul, d.Xo₂.univ.eta_ker, MonObj.comp_one]
    rw [hMb, ← Nat.cast_smul_eq_nsmul (𝓞 E), Submodule.mul_smul]
    exact Submodule.smul_mem_smul (LevelPoints.natCast_mem l) hq
  have h₂ : levPt Xo x₀ x ^ l.M = 1 := by
    rw [levPt, ← MonObj.comp_pow, LevelPoints.eta_pow, MonObj.comp_one]
  have h₃ : e (levPt d.Xo₂ x₂ q) ^ d.pd = levPt Xo x₀ x ^ d.pd := by
    have a : Xo.univ.eta q = Xo.univ.eta x ^ d.pd := by
      have := Xo.univ.eta_add (q - (d.pd : 𝓞 E) • x) ((d.pd : 𝓞 E) • x)
      rwa [sub_add_cancel, Xo.univ.eta_ker _ hx, _root_.one_mul, Nat.cast_smul_eq_nsmul,
        LevelPoints.eta_nsmul] at this
    rw [← map_pow, levPt, levPt, ← MonObj.comp_pow, ← MonObj.comp_pow, ← a]
    refine Over.OverMorphism.ext ?_
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, heta, Over.toUnit_left, Over.toUnit_left]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h0)
  refine ⟨h₁, ?_⟩
  have h₄ : e (levPt d.Xo₂ x₂ q) ^ l.M = levPt Xo x₀ x ^ l.M := by rw [← map_pow, h₁, map_one, h₂]
  rw [← div_eq_one, ← pow_one (_ / _), ← hcop, pow_gcd_eq_one, div_pow, div_pow, h₃, h₄, div_self', div_self']
  exact ⟨rfl, rfl⟩

theorem exists_column (hd : d.IsLev) {S : Type} [CommRing S] {x₂ : Sp S ⟶ d.Xo₂.X} {x₀ : Sp S ⟶ Xo.X}
    (h0 : x₂ ≫ d.r = x₀) {w : LB.Iso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ)} (hw : FrameLift.IsRig d w)
    {p : Gx x₂ ⟶ Gx x₀}
    (p₂ : p ≫ (snd (Over.mk x₀) Xo.univ.t.G).left = (snd (Over.mk x₂) d.Xo₂.univ.t.G).left ≫ d.m.φ)
    (p₁ : p ≫ (fst (Over.mk x₀) Xo.univ.t.G).left = (fst (Over.mk x₂) d.Xo₂.univ.t.G).left)
    {s₂ : LB.Sec (PPx x₂)} {s : LB.Sec (PPx x₀)}
    (hs : FrameLift.Rel (q₂ := (snd (Over.mk x₂) d.Xo₂.univ.t.G).left) (q := (snd (Over.mk x₀) Xo.univ.t.G).left)
      w p s₂ s) {q x : Dw.La} (hq : q ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La))
    (hx : q - (d.pd : 𝓞 E) • x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) {κ : ℕ} (hN : Odd (l.M * κ))
    {t : ptO d.Xo₂ x₂ ⟶ d.Xo₂.univ.t.G} (ht : t ^ (l.M * κ) = levPt d.Xo₂ x₂ q) {j : ℕ}
    (hj : KilledBy d.Xo₂ (d.l₂.Mb ^ j) t) :
    ∃ G G₂, IsVtOver Xo.univ.t.G Xo.univ.t.PP l.M (KilledBy Xo (l.Mb ^ 2)) s (levPt Xo x₀ x) G ∧
      TranslMove.SecRel (T := ptO d.Xo₂ x₂) (T₀ := ptO Xo x₀) w p G G₂ ∧
      ∀ z F, z ^ (l.M * κ) = 1 → IsUUOver d.Xo₂.univ.t.G d.Xo₂.univ.t.PP (l.M * κ) s₂ z t F →
        Pulls d.Xo₂ (κ : 𝓞 E) (sqN d.Xo₂ l.M G₂) (sqN d.Xo₂ (l.M * κ) F) := by
  have hLaw : Laws := GlobalTheory.abelianSchemeLaws_all.1
  obtain ⟨e, he⟩ := FrameLift.exists_push d.m.cart h0
  obtain ⟨a₁, a₂⟩ := levPt_push d hd h0 e he hq hx
  have b₁ : (t ^ κ) ^ l.M = levPt d.Xo₂ x₂ q := by rw [← pow_mul, mul_comm, ht]
  have b₂ : (t ^ κ) ^ l.M ^ 2 = 1 := by rw [sq, pow_mul, b₁, a₁]
  have b₃ : t ^ (l.M * κ) ^ 2 = 1 := by rw [sq, pow_mul, ht, pow_mul, a₁, one_pow]
  have b₄ : e (t ^ κ) ^ l.M = levPt Xo x₀ x := by rw [← map_pow, b₁, a₂]
  have b₅ : e (t ^ κ) ^ l.M ^ 2 = 1 := by rw [← map_pow, b₂, map_one]
  have hact : ∀ u b, e (u ≫ d.Xo₂.univ.t.act.act b) = e u ≫ Xo.univ.t.act.act b := fun u b =>
    Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc, d.m.act])
  have b₆ : KilledBy Xo (l.Mb ^ 2) (e (t ^ κ)) := by
    refine killedBy_sq (J := d.l₂.Mb ^ j) (fun b hb => ?_) ?_ fun b hb => ?_
    · rw [b₄, levPt, Category.assoc, (GlobalTheory.moduli_univ_eta_killed hLaw E H Dw l Xo x).1 b hb, MonObj.comp_one]
    · refine Ideal.pow_sup_eq_top (top_le_iff.1 (d.l₂.coprime.ge.trans (sup_le_sup_left (Ideal.map_mono hd.1.2.1) _)))
    · rw [← hact, ← comp_act_natCast, Category.assoc, ← d.Xo₂.univ.t.act.mul, hj _ (Ideal.mul_mem_left _ _ hb),
        map_one]
  obtain ⟨G, hG⟩ := exists_vt l.odd s b₅
  obtain ⟨t', -, rfl, hU⟩ := (uu_through_moves E H Dw l Xo S x₀ _ l.odd s).2 _ _ G
    (by rw [← pow_mul, ← sq, b₅]) hG
  have := UnivPol.isLocallyNoetherian d.Xo₂
  have hρ := (maps_iff w _ (fun _ => eSec Xo.univ.t.G) _ d.Xo₂.univ.t.PP.rig Xo.univ.t.PP.rig d.m.cm.e _
    (rigPull_le d.m.cm.F d.m.cm.e d.m.cm.e_comm Xo.univ.t.PP.L) (fun _ => rfl)).1 hw.2
  have hR : TranslMove.SecRel (T := ptO d.Xo₂ x₂) (T₀ := ptO Xo x₀) w p s s₂ := fun Z r z J₀ J hJ₀ hJ => by
    refine (sval_of s (r ≫ p) z J₀ (fun _ => J₀ ((r ≫ (snd (Over.mk x₂) d.Xo₂.univ.t.G).left) ≫ d.m.φ))
      (fun _ => by rw [Category.assoc, p₂, Category.assoc])).trans ?_
    rw [zpow_one]
    exact hs Z r z _ _ (hJ₀ ((r ≫ (snd (Over.mk x₂) d.Xo₂.univ.t.G).left) ≫ d.m.φ))
      (hJ (r ≫ (snd (Over.mk x₂) d.Xo₂.univ.t.G).left))
  obtain ⟨G₂, hG₂, hR₂⟩ := TranslMove.exists_isUUOver d.m.cart (T := ptO d.Xo₂ x₂) (T₀ := ptO Xo x₀) (τ := 𝟙 (Sp S))
    hw.1 (p₁.trans (Category.comp_id _).symm) p₂ d.m.cm.e_comm hρ l.M
    (fun θ => TranslMove.pt_pow_eq_one hLaw.kerPow (UnivPol.pol d.Xo₂) (l.M ^ 2) (Nat.cast_pow l.M 2).symm θ) hR
    (x₁ := 1) (x₂ := t ^ κ) ((Category.id_comp _).trans (by rw [← he, map_one]))
    ((Category.id_comp _).trans (he _)) hU
  refine ⟨G, G₂, ?_, hR₂, fun z F hz hF => pulls_of_uu hN s₂ hz b₃ b₂ hF hG₂⟩
  obtain ⟨t', α₀, α, s₁, U, -, rfl, hrest⟩ := hG
  exact ⟨_, α₀, α, s₁, U, b₄, b₆, hrest⟩

end Cover

theorem nrm_natCast (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (κ : ℕ) :
    nrm Dw c a (κ : 𝓞 E) = (κ : c.F) ^ (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), a (τ, i)) := by
  have h := AlphaForm.nrm_mul_nrm Dw c a (κ : 𝓞 E) 1 κ (_root_.mul_one _)
  have h₁ : nrm Dw c a 1 = 1 := by simp [nrm]
  rwa [h₁, _root_.mul_one] at h

theorem exists_value [StarRing (𝓞 E)] {nab : NabV Xo c} {n : ℕ} {d : DeltaDat Xo c n} (hd : d.IsLev)
    (hn : IsNab Xo c nab) (hn₂ : IsNab d.Xo₂ d.c₂ d.nab₂) {m N : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {x q : Fin m → Dw.La}
    {P : MvPolynomial (LtN Dw m) c.F} (hN : Odd N) (hMN : l.M ∣ N) (hP : P ∈ harmA c a m)
    (hq : ∀ b, q b ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧
      q b - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La))
    {k : Type} [Field k] [Algebra c.F k] [Algebra d.c₂.F k]
    (hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) {y : FrPt Xo c k} {y₂ : FrPt d.Xo₂ d.c₂ k}
    (hy : FrOver d y₂ y) {t : Fin m → (ptO d.Xo₂ y₂.x ⟶ d.Xo₂.univ.t.G)}
    (ht : ∀ b, t b ^ N = levPt d.Xo₂ y₂.x (q b) ∧ ∃ j : ℕ, KilledBy d.Xo₂ (d.l₂.Mb ^ j) (t b)) :
    ∃ v, ThValAt Xo c nab y x P v ∧ ∀ (z : Fin m → (ptO d.Xo₂ y₂.x ⟶ d.Xo₂.univ.t.G))
      (F : Fin m → LB.Sec (LPow d.Xo₂.univ.t.G d.Xo₂.univ.t.PP.L ((N : ℤ) ^ 2) (ptO d.Xo₂ y₂.x))),
      (∀ b, z b ^ N = 1) → (∀ b, IsUUOver d.Xo₂.univ.t.G d.Xo₂.univ.t.PP N y₂.s (z b) (t b) (F b)) →
      ∑ e ∈ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).support,
        algebraMap d.c₂.F k ((MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).coeff e) *
          ∏ b, d.nab₂ y₂ ((N : ℤ) ^ 2) (F b) (colOf e b) =
        (N : k) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree * v := by
  obtain ⟨κ, rfl⟩ := hMN
  obtain ⟨h0, hu, w, p, hw, p₂, p₁, hs⟩ := (FrameLift.frOver_iff d _ _).1 hy
  choose j hj using fun b => (ht b).2
  choose G G₂ hG hR hpl using fun b => exists_column d hd h0 hw p₂ p₁ hs (hq b).1 (hq b).2 hN (ht b).1 (hj b)
  refine ⟨thExpr Xo c nab y P G, ⟨k, inferInstance, inferInstance, AlgHom.id _ _, y, G,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id, PullbackSections.frMap_refl y, hG, rfl⟩, fun z F hz hF => ?_⟩
  have hs' : Function.Surjective (d.eF : c.F →+* d.c₂.F) := fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩
  have hk' : ∀ t : c.F, algebraMap d.c₂.F k ((d.eF : c.F →+* d.c₂.F) t) = algebraMap c.F k t := hk
  generalize (d.eF : c.F →+* d.c₂.F) = f at hs' hk' ⊢
  have hP₂ : MvPolynomial.map f P ∈ HH d.c₂ a m := GlobalTheory.map_mem_HHa Dw.mult m f hs' _ _ _ P hP.1
  have lin := (hv_linear E H Dw d.l₂ d.Xo₂ d.c₂ hn.1 d.nab₂ hn₂ k y₂ m (MvPolynomial.map f P)).2.2
  have e₁ := hv_push hn hn₂ d.m h0 p₁ p₂ hw.1 hw.2 hu f hk' hP.1 (l.M ^ 2) _ (Nat.cast_pow l.M 2).symm G G₂ hR
  have e₂ := hv_pulls E H Dw d.l₂ d.Xo₂ d.c₂ hn.1 d.nab₂ hn₂ k y₂ (κ : 𝓞 E) (κ ^ 2) (l.M ^ 2) ((l.M * κ) ^ 2)
    (natCast_mul_bar H κ) (mul_pow _ _ _) m _ _ (fun b => hpl b (z b) (F b) (hz b) (hF b)) a _ hP₂
  rw [lin, e₂, ← lin, ← e₁, thExpr]
  by_cases hP0 : P = 0
  · simp [hP0]
  have hdeg : (MvPolynomial.map f P).totalDegree = P.totalDegree := by
    rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective P f.injective]
  have : CharZero k := charZero_of_injective_algebraMap (algebraMap c.F k).injective
  have hM : (l.M : k) ≠ 0 := Nat.cast_ne_zero.2 l.odd.pos.ne'
  rw [nrm_natCast, ← AlphaForm.totalDegree_harm c hP hP0, hdeg]
  simp only [map_inv₀, map_pow, map_natCast, Nat.cast_mul, mul_pow]
  field_simp

end GlobalTheory.StdCover

open GlobalTheory.StdCover in
open scoped Classical in

theorem GlobalTheory.shortValAt_std_cover_eq_thValAt : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → IsNab Xo c nab → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ (m N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (x : Fin m → Dw.La) (P : MvPolynomial (LtN Dw m) c.F) (q₀ : Fin m → LevQ Dw d.l₂), GenLat.LevOK (⟨stdLat E m⟩ : GenLat E m) N d.l₂.M → P ∈ harmA c a m → (∀ b, levRep (q₀ b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧ levRep (q₀ b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) → ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∀ v v' : k, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q : Fin m → LevQ Dw d.l₂ => if q = q₀ then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) (⟨stdLat E m⟩ : GenLat E m) 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) y₂ v → ThValAt Xo c nab y x P v' → v = v' := by
  intro hCI E _ _ _ H Dw l Xo c _ nab n d hd hn hn₂ m N a x P q₀ hN hP hq k _ _ _ _ hk y y₂ hy v v' hv hv'
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := ShortAtField.finite_levQ Dw d.l₂
  obtain ⟨S₁, _, _, φ₁, y₁, z₁, t₁, F₁, hf₁, hm₁, hz₁, hg₁, ht₁, hu₁, e₁⟩ := hv
  beta_reduce at e₁
  have : Nontrivial S₁ := hf₁.injective.nontrivial
  obtain ⟨Ω, _, _, ⟨χ⟩⟩ := ShortAtField.exists_algHom_field d.c₂.F S₁
  obtain ⟨u₂, hu₂⟩ := FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂ S₁ Ω χ y₁
  have hP₂ : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ HH d.c₂ a m :=
    GlobalTheory.map_mem_HHa Dw.mult m (d.eF : c.F →+* d.c₂.F) (fun y => ⟨d.eF.symm y, d.eF.apply_symm_apply y⟩) _ _ _ P hP.1
  obtain ⟨z, t, F, hz, -, ht, hF, e₂⟩ :=
    ShortAtField.exists_pull d.nab₂ hn₂ _ N a _ hP₂ χ y₁ u₂ hu₂ z₁ t₁ F₁ hz₁ hg₁ ht₁ hu₁
  let _ : Algebra c.F Ω := ((algebraMap d.c₂.F Ω).comp (d.eF : c.F →+* d.c₂.F)).toAlgebra
  let ψ : k →ₐ[c.F] Ω := ⟨(χ.comp φ₁).toRingHom, fun r => by
    rw [← hk]; exact (χ.comp φ₁).commutes _⟩
  obtain ⟨u, hu⟩ := FramedBaseChange.exists_frMap hL E H Dw l Xo c k Ω ψ y
  have hy' : FrOver d u₂ u :=
    FrameLift.frOver_map d (ψ := ψ) (ψ₂ := χ.comp φ₁) rfl hy hu (FramedBaseChange.trans φ₁ χ hm₁ hu₂)
  obtain ⟨w, hw, e₃⟩ := exists_value hd hn hn₂ hN.1 (hd.1.1.trans hN.2.1) hP hq (fun _ => rfl) hy' (ht q₀)
  have e₄ := GlobalTheory.thetaValue_natural hL hCI E H Dw l Xo c nab hn k Ω ψ y u hu a m x P hP v' w hv' hw
  apply ψ.toRingHom.injective
  change χ (φ₁ v) = ψ v'
  rw [e₄, e₁, finsum_eq_single _ q₀ (fun q hq => by rw [if_neg hq, map_zero, zero_mul]), if_pos rfl, map_mul,
    map_mul χ, e₂, χ.commutes, χ.commutes,
    Finset.sum_congr rfl fun i _ => e₃ (z i) (F q₀ i) (pow_eq_one_of_inZh (hz i)) (hF q₀ i),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h₁ : GenLat.zCard (⟨stdLat E m⟩ : GenLat E m) N (Dw.p + Dw.q) =
      GenLat.mIdx (⟨stdLat E m⟩ : GenLat E m) N (Dw.p + Dw.q) := by
    unfold GenLat.zCard GenLat.mIdx GenLat.Ln
    rw [inf_idem]
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap d.c₂.F Ω).injective
  have h₂ : (GenLat.mIdx (⟨stdLat E m⟩ : GenLat E m) N (Dw.p + Dw.q) : Ω) ≠ 0 := Nat.cast_ne_zero.2
    (TrivLattice.index_part _ N _ 2 1 hN Nat.prime_two (Nat.coprime_one_left 2) (fun v hv => by rwa [one_smul]) _).2
  have h₃ : (Nat.card (Fin m → LevQ Dw d.l₂) : Ω) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have h₄ : (N : Ω) ≠ 0 := Nat.cast_ne_zero.2 hN.1.pos.ne'
  rw [h₁, nsmul_eq_mul]
  simp only [map_mul, map_inv₀, map_natCast, map_pow, map_one]
  field_simp
end
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardCover_shortValue_eq_thetaValue : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → IsNab Xo c nab → IsNab d.Xo₂ d.c₂ d.nab₂ → ∀ (m N : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (x : Fin m → Dw.La) (P : MvPolynomial (LtN Dw m) c.F) (q₀ : Fin m → LevQ Dw d.l₂), GenLat.LevOK (⟨stdLat E m⟩ : GenLat E m) N d.l₂.M → P ∈ harmA c a m → (∀ b, levRep (q₀ b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧ levRep (q₀ b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)) → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k], (∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t) → ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∀ v v' : k, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q : Fin m → LevQ Dw d.l₂ => if q = q₀ then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) (⟨stdLat E m⟩ : GenLat E m) 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) y₂ v → ThValAt Xo c nab y x P v' → v = v' := by
  atlas_forward_decl GlobalTheory.shortValAt_std_cover_eq_thValAt
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShortTimesTheta

section General

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.FormTies GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev ConjQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

theorem card_quot (Dw : Datum H) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) :
    Nat.card (Dw.La ⧸ (I • ⊤ : Submodule (𝓞 E) Dw.La)) = Ideal.absNorm I ^ (Dw.p + Dw.q) := by
  haveI := Dw.fin
  haveI := Dw.proj
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  rw [natCard_quot_smul_top_of_projective, Dw.rank, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem mb_ne_bot (l : Level H) : l.Mb ≠ ⊥ ∧ Mfr l ≠ ⊥ := by
  have hM : (l.M : 𝓞 E) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have h : l.Mb * Mfr l ≠ ⊥ := by
    rw [Mfr, l.prod, Ne, Ideal.span_singleton_eq_bot]; exact hM
  exact ⟨fun e => h (by rw [e, Ideal.bot_mul]), fun e => h (by rw [e, Ideal.mul_bot])⟩

theorem finite_conjQ (Dw : Datum H) (l : Level H) : Finite (ConjQ Dw l) :=
  Nat.finite_of_card_ne_zero (by
    rw [card_quot Dw (mb_ne_bot l).2]
    exact pow_ne_zero _ (fun h => (mb_ne_bot l).2 (Ideal.absNorm_eq_zero_iff.1 h)))

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem card_cover {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) :
    Nat.card (LevQ Dw d.l₂) = Nat.card (ConjQ Dw l) * Nat.card (LaI Xo c d) := by
  have hI : d.I ≠ ⊥ := fun e => (mb_ne_bot d.l₂).1 (by rw [hd.2.2.2.1, e, Ideal.mul_bot])
  have h1 : Ideal.absNorm (Mfr l) = Ideal.absNorm l.Mb := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv l.Mb _ H.bar rfl).toEquiv).symm
  rw [card_quot Dw (mb_ne_bot d.l₂).1, card_quot Dw (mb_ne_bot l).2, card_quot Dw hI, hd.2.2.2.1, map_mul, mul_pow, h1]

theorem pd_mem {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) : (d.pd : 𝓞 E) ∈ d.I ∧ l.Mb ⊔ d.I = ⊤ := by
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have h2 := d.l₂.prod
  rw [hd.2.2.2.1, hd.2.1, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
    ← Ideal.span_singleton_mul_span_singleton] at h2
  have h3 := mul_left_cancel₀ (by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM) h2
  have h4 : (d.pd : 𝓞 E) ∈ d.I := by
    have : Ideal.span {(d.pd : 𝓞 E)} ≤ d.I := h3 ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  have h5 : (l.M : 𝓞 E) ∈ l.Mb := by
    have : Ideal.span {(l.M : 𝓞 E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact this (Ideal.subset_span rfl)
  refine ⟨h4, ?_⟩
  obtain ⟨u, v, huv⟩ := Nat.Coprime.cast (R := 𝓞 E) hd.2.2.1
  rw [Ideal.eq_top_iff_one, ← huv, add_comm]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ h5) (Ideal.mul_mem_left _ _ h4)

theorem eq_mk_iff {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) (x : Dw.La) (q : LevQ Dw d.l₂) :
    q = Submodule.Quotient.mk ((d.pd : 𝓞 E) • x) ↔ levRep q ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) ∧
      levRep q - (d.pd : 𝓞 E) • x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
  obtain ⟨h1, h2⟩ := pd_mem d hd
  have hq : Submodule.Quotient.mk (levRep q) = q := Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  have hp : (d.pd : 𝓞 E) • x ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) := Submodule.smul_mem_smul h1 trivial
  conv_lhs => rw [← hq, Submodule.Quotient.eq, hd.2.2.2.1]
  constructor
  · intro h
    refine ⟨?_, Submodule.smul_mono_left Ideal.mul_le_left h⟩
    simpa using add_mem (Submodule.smul_mono_left Ideal.mul_le_right h) hp
  · rintro ⟨ha, hb⟩
    have hc := sub_mem ha hp
    generalize levRep q - (d.pd : 𝓞 E) • x = v at hb hc
    obtain ⟨a, ha, b, hb', hab⟩ := Submodule.mem_sup.1 (h2 ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ l.Mb ⊔ d.I)
    have e : v = a • v + b • v := by rw [← add_smul, hab, one_smul]
    rw [e]
    refine add_mem ?_ ?_
    · rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul ha hc
    · rw [mul_comm, Submodule.mul_smul]; exact Submodule.smul_mem_smul hb' hb

theorem sum_char [inst : Fintype (ConjQ Dw l)] (c : Coeff l) {m : ℕ} (u v : Fin m → Dw.La) :
    ∑ x : Fin m → ConjQ Dw l, zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) u) *
        zetaM c ^ pairL (l := l) (fun b => qRep (x b)) v =
      if ∀ b, v b - u b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (ConjQ Dw l) : c.F) ^ m else 0 := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have hz := LevelPairing.zetaM_prim c
  have h0 : zetaM c ≠ 0 := hz.ne_zero hM.ne'
  have h1 : ∀ x : Fin m → ConjQ Dw l, zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) u) *
        zetaM c ^ pairL (l := l) (fun b => qRep (x b)) v =
      ∏ b, zetaM c ^ Dw.EF (qRep (x b)) (cSep l • (v b - u b)) := fun x => by
    rw [← zpow_add₀ h0, ← MoreColumns.zpow_sum h0]
    congr 1
    simp only [pairL, smul_sub, map_sub, Finset.sum_sub_distrib]
    ring
  have h2 : ∀ w : Dw.La, ∑ a : ConjQ Dw l, zetaM c ^ Dw.EF (qRep a) (cSep l • w) =
      if w ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (ConjQ Dw l) : c.F) else 0 := fun w =>
    @MoreColumns.char_sum E _ _ _ H Dw l.M hM l.Mb l.prod l.coprime c.F _ _ hz inst w
  simp only [h1]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ)
    (fun b (a : ConjQ Dw l) => zetaM c ^ Dw.EF (qRep a) (cSep l • (v b - u b)))]
  simp only [h2]
  rw [Finset.prod_ite_zero]
  simp

theorem sum_new_columns [Fintype (ConjQ Dw l)] {n : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev) {m : ℕ} (x : Fin m → Dw.La)
    (q : Fin m → LevQ Dw d.l₂) :
    (∑ x' : Fin m → ConjQ Dw l, zetaM c ^ (-pairL (l := l) (fun b => qRep (x' b)) (fun b => (d.pd : 𝓞 E) • x b)) *
        zetaM c ^ pairL (l := l) (fun b => qRep (x' b)) (fun b => levRep (q b))) *
      (if ∀ b : Fin m, levRep (q b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then (Nat.card (LaI Xo c d) : c.F) ^ m else 0) =
      if q = fun b => Submodule.Quotient.mk ((d.pd : 𝓞 E) • x b) then (Nat.card (Fin m → LevQ Dw d.l₂) : c.F) else 0 := by
  rw [sum_char, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, card_cover d hd]
  simp only [funext_iff, eq_mk_iff d hd, forall_and]
  by_cases h1 : ∀ b, levRep (q b) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) <;>
    by_cases h2 : ∀ b, levRep (q b) - (d.pd : 𝓞 E) • x b ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) <;>
    simp [h1, h2, mul_pow]

theorem weighted_sum {K S ι Q : Type} [Field K] [CommRing S] [Algebra K S] [Fintype ι] [Finite Q] (cf : ι → K)
    (w : ι → Q → K) (w₀ : Q → K) (t : K) (hw : ∀ q, ∑ i, cf i * w i q = t * w₀ q) (A : S) (B : Q → S) :
    ∑ i, algebraMap K S (cf i) * (A * ∑ᶠ q, algebraMap K S (w i q) * B q) =
      algebraMap K S t * (A * ∑ᶠ q, algebraMap K S (w₀ q) * B q) := by
  haveI := Fintype.ofFinite Q
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_left_comm, ← mul_assoc (algebraMap K S t), ← map_mul, ← hw, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]; ring

theorem shortVal_sum (hC : ChartIndepSt2) [StarRing (𝓞 E)] {nab : NabV Xo c} (hn : IsNab Xo c nab) {n : ℕ}
    {Λ : GenLat E n} {N : ℕ} (hU : Λ.Unimod) (hT : Λ.TrivAt l.M) (hL : Λ.LevOK N l.M) {a : (E →+* ℂ) × ℕ → ℕ}
    {P : MvPolynomial (LtN Dw n) c.F} (hP : P ∈ harmL c Λ a) {ι : Type} [Fintype ι] (cf : ι → c.F)
    (w : ι → (Fin n → LevQ Dw l) → c.F) (w₀ : (Fin n → LevQ Dw l) → c.F) (t : c.F)
    (hw : ∀ q, ∑ i, cf i * w i q = t * w₀ q) (β : c.F) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (v : S) (u : ι → S) (hv : ShortValAt Xo c nab w₀ Λ β N P y v)
    (hu : ∀ i, ShortValAt Xo c nab (w i) Λ β N P y (u i)) :
    ∑ i, algebraMap c.F S (cf i) * u i = algebraMap c.F S t * v := by
  haveI := ShortValue.finite_levelQuotient Dw l
  obtain ⟨S', _, _, φ, y', z, tp, F, h1, h2, h3, h4, h5, h6, h7⟩ := hv
  have hinj : Function.Injective φ := h1.injective
  apply hinj
  have key := fun i => (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.abelianSchemeLaws_all.1 hC E H Dw l Xo c nab hn n
    Λ N hU hT hL a P hP.1 (w i) β).2 S S' φ y y' h2 (u i) _ (hu i)
    ⟨S', _, _, AlgHom.id c.F S', y', z, tp, F, RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      FramedBaseChange.refl y', h3, h4, h5, h6, rfl⟩
  rw [map_sum, map_mul, h7]
  simp only [map_mul φ, AlgHom.commutes, key]
  exact weighted_sum cf w w₀ t hw _ _

theorem admissibleColumns_append {n m nV : ℕ} (h : n = nV → m = 0) (x0 : Fin n → Dw.La) (x : Fin m → Dw.La)
    (hx : AdmX (l := l) (decide (n = nV)) x0) : AdmX (l := l) (decide (n + m = nV)) (Fin.append x0 x) := by
  unfold AdmX at hx ⊢
  refine eq_top_iff.2 (hx.ge.trans (sup_le_sup_right (Submodule.span_mono ?_) _))
  rintro _ ⟨b, hb, rfl⟩
  refine ⟨Fin.castAdd m b, ?_, Fin.append_left _ _ _⟩
  rcases hb with hb | hb
  · have h1 : n = nV := of_decide_eq_true hb
    exact Or.inl (decide_eq_true (by have := h h1; omega))
  · exact Or.inr hb

theorem trivAt_of_dvd {n a b : ℕ} {Λ : GenLat E n} (h : Λ.TrivAt b) (hab : a ∣ b) : Λ.TrivAt a := by
  obtain ⟨k, hk, h⟩ := h
  exact ⟨k, hk.coprime_dvd_right hab, h⟩

theorem isBeta_betaH {n : ℕ} {Λ : GenLat E n}
    (h : ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) :
    IsBeta Dw c Λ (betaH (Dw := Dw) c Λ) := by
  unfold betaH
  rw [dif_pos h]
  exact h.choose_spec

theorem map_blockPoly {K K' : Type} [Field K] [Field K'] (f : K →+* K') {n m : ℕ} (P : MvPolynomial (LtN Dw n) K)
    (Q : MvPolynomial (LtN Dw m) K) :
    MvPolynomial.map f (blockPoly P Q) = blockPoly (MvPolynomial.map f P) (MvPolynomial.map f Q) := by
  simp only [blockPoly, map_mul, MvPolynomial.map_rename]

theorem isIntegral_zpow {K : Type} [Field K] {ζ : K} (h : IsOfFinOrder ζ) (t : ℤ) : IsIntegral ℤ (ζ ^ t) := by
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  refine IsIntegral.of_pow hk ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, e, one_zpow]
  exact isIntegral_one

theorem starRing_eq {R : Type} [CommRing R] (s t : StarRing R) (h : ∀ a, s.star a = t.star a) : s = t := by
  obtain @⟨@⟨@⟨⟨f⟩, _⟩, _⟩, _⟩ := s
  obtain @⟨@⟨@⟨⟨g⟩, _⟩, _⟩, _⟩ := t
  obtain rfl : f = g := funext h
  rfl

theorem sum_data [Fintype (ConjQ Dw l)] {n m : ℕ} (d : DeltaDat Xo c n) (hd : d.IsLev)
    (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F) (ζ : c.F)
    (hφ : ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) *
      (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then
        (Nat.card (LaI Xo c d) : c.F) ^ m else 0))
    (x0 : Fin n → Dw.La) (x : Fin m → Dw.La) (q : Fin (n + m) → LevQ Dw d.l₂) :
    ∑ x' : Fin m → ConjQ Dw l,
        d.eF (zetaM c ^ (-pairL (l := l) (fun b => qRep (x' b)) (fun b => (d.pd : 𝓞 E) • x b))) *
          d.eF (zetaM c ^ pairL (l := l) (Fin.append x0 fun b => qRep (x' b)) (fun b => levRep (q b)) * φ' q) =
      d.eF ζ * blockDat (d.w x0) (fun q : Fin m → LevQ Dw d.l₂ =>
        if q = fun b => Submodule.Quotient.mk ((d.pd : 𝓞 E) • x b) then (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F)
        else 0) q := by
  have hM : 0 < l.M := by have := l.three_le; omega
  have h0 : zetaM c ≠ 0 := (LevelPairing.zetaM_prim c).ne_zero hM.ne'
  have h1 : ∀ y : Fin m → Dw.La, zetaM c ^ pairL (l := l) (Fin.append x0 y) (fun b => levRep (q b)) =
      zetaM c ^ pairL (l := l) x0 (fun b => levRep (q (Fin.castAdd m b))) *
        zetaM c ^ pairL (l := l) y (fun b => levRep (q (Fin.natAdd n b))) := fun y => by
    rw [← zpow_add₀ h0]
    congr 1
    simp [pairL, Fin.sum_univ_add]
  have h2 := congrArg d.eF (sum_new_columns d hd x (fun b => q (Fin.natAdd n b)))
  rw [apply_ite d.eF, map_natCast, map_zero] at h2
  unfold blockDat
  refine Eq.trans ?_ (congrArg (fun t => d.eF ζ * (d.w x0 (fun i => q (Fin.castAdd m i)) * t)) (h2.trans (by congr)))
  simp only [h1, hφ, DeltaDat.w, ← map_mul, ← map_sum]
  congr 1
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

theorem mul_mem_span (hC : ChartIndepSt2) [StarRing (𝓞 E)] {nab : NabV Xo c} (hn : IsNab Xo c nab) {n m : ℕ}
    (d : DeltaDat Xo c n) (hd : d.IsLev) (hn₂ : IsNab d.Xo₂ d.c₂ d.nab₂) (φ' : (Fin (n + m) → LevQ Dw d.l₂) → c.F)
    (ζ : c.F) (hζ : IsOfFinOrder ζ)
    (hφ : ∀ q : Fin (n + m) → LevQ Dw d.l₂, φ' q = ζ * d.φδ (fun b => q (Fin.castAdd m b)) *
      (if ∀ b : Fin m, levRep (q (Fin.natAdd n b)) ∈ (d.I • ⊤ : Submodule (𝓞 E) Dw.La) then
        (Nat.card (LaI Xo c d) : c.F) ^ m else 0))
    (bad nV : ℕ) (hV : n = nV → m = 0)
    (hβ : ∀ (k : ℕ) (Λ : GenLat E k), Λ.Unimod → Λ.TrivAt bad →
      ∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (hT : ShortValTot Xo c nab bad nV (a + a') (n + m) (withCoeff d φ'))
    {g f : Rul Xo c} (hg : g ∈ shortGen Xo c nab bad nV a n d) (hf : f ∈ thGen Xo c nab a' m) :
    g * f ∈ Submodule.span (𝓞 c.F) (shortGen Xo c nab bad nV (a + a') (n + m) (withCoeff d φ')) := by
  haveI := finite_conjQ Dw l
  haveI := Fintype.ofFinite (ConjQ Dw l)
  have hLaws := GlobalTheory.abelianSchemeLaws_all.1
  have hM : 0 < l.M := by have := l.three_le; omega
  have hfs := GlobalTheory.thetaRule_mem_sec hLaws hC E H Dw l Xo c nab hn a' m f hf
  obtain ⟨hgs, Λ, N, x0, P', hU, hb, hT₂, hL₂, hx0, hP', hgr⟩ := hg
  obtain ⟨x, P, hP, hfr⟩ := hf
  have hdv : l.M ∣ d.l₂.M := hd.1.1
  have hPL : P ∈ harmL c (unitLat E m) a' := (StdHarm.harmL_std c m a').ge hP
  have hA : LatAdm l bad Λ := ⟨hU, hb, trivAt_of_dvd hT₂ hdv⟩
  have hA₂ : LatAdm d.l₂ bad Λ := ⟨hU, hb, hT₂⟩
  have hu₂ : (unitLat E m).LevOK N d.l₂.M :=
    ⟨hL₂.1, hL₂.2.1, by simpa [GenLat.Ln, unitLat] using Submodule.smul_le_right⟩
  have hQ := ((GlobalTheory.shortSeries_blockProduct hC E H Dw l Xo c nab hn bad n m Λ _ hA (Survey.BaseClassMove.latAdm_unit l bad m) N
    ⟨hL₂.1, hdv.trans hL₂.2.1, hL₂.2.2⟩ ⟨hu₂.1, hdv.trans hu₂.2.1, hu₂.2.2⟩).2 a a' P' P hP' hPL).1
  obtain ⟨⟨hB, hBL⟩, hprod⟩ := GlobalTheory.shortSeries_blockProduct hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn₂ bad n m Λ _ hA₂
    (Survey.BaseClassMove.latAdm_unit d.l₂ bad m) N hL₂ hu₂
  have b₁ := isBeta_betaH (hβ n Λ hU hb)
  have b₂ := isBeta_betaH (hβ _ _ hB.1 hB.2.1)
  obtain ⟨ζ', hζ', eβ⟩ := ((BetaOfSum.blockBeta E H Dw l c bad).1 n m Λ _ hA (Survey.BaseClassMove.latAdm_unit l bad m) _ 1 _ b₁
    (Survey.BaseClassMove.isBeta_unit c m)).1 b₂
  have hadm := fun x' : Fin m → ConjQ Dw l => admissibleColumns_append hV x0 (fun b => qRep (x' b)) hx0
  choose F hFs hFr using fun x' : Fin m → ConjQ Dw l =>
    (hT (blockLat Λ (unitLat E m)) N _ _ hB.1 hB.2.1 hB.2.2 hBL (hadm x') hQ).2
  have hζ0 : ζ ≠ 0 := hζ.isUnit.ne_zero
  let cf : (Fin m → ConjQ Dw l) → c.F := fun x' =>
    zetaM c ^ (-pairL (l := l) (fun b => qRep (x' b)) (fun b => (d.pd : 𝓞 E) • x b))
  have hcf : ∀ x', IsIntegral ℤ (ζ' * ζ⁻¹ * cf x') := fun x' =>
    ((by simpa using isIntegral_zpow hζ' 1 : IsIntegral ℤ ζ').mul
      (by simpa using isIntegral_zpow hζ (-1) : IsIntegral ℤ ζ⁻¹)).mul
      (isIntegral_zpow (isOfFinOrder_iff_pow_eq_one.2 ⟨l.M, hM, (LevelPairing.zetaM_prim c).pow_eq_one⟩) _)
  have main : g * f = ∑ x', (ζ' * ζ⁻¹ * cf x') • F x' := by
    refine ClassSumUnique.sec_eq_of_geometric (sec_mul Xo c a a' n m hgs hfs)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hFs i)) fun k _ _ _ y => ?_
    letI iA : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t := fun t => by
      show algebraMap c.F k (d.eF.symm (d.eF t)) = _
      rw [AlgEquiv.symm_apply_apply]
    obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
    obtain ⟨v₁, hv₁, e₁⟩ := hgr k hk y y₂ hy
    choose u hu eu using fun x' => @hFr x' k _ _ _ iA hk y y₂ hy
    have hP₁ := ((PlaceInt.eF_transfer E H Dw l Xo c n d Λ).2.1 a P' hP').1
    have hP₂ : MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P ∈ harmL d.c₂ (unitLat E m) a' :=
      ((PlaceInt.eF_transfer E H Dw l Xo c m (withCoeff d fun _ => 0) (unitLat E m)).2.1 a' P hPL).1
    obtain ⟨v₂, hv₂, -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural hLaws hC E H Dw d.l₂ d.Xo₂ d.c₂ d.nab₂ hn₂ m
      (unitLat E m) N (Survey.BaseClassMove.latAdm_unit d.l₂ bad m).1 (Survey.BaseClassMove.latAdm_unit d.l₂ bad m).2.2 hu₂ a' _ hP₂.1
      (fun q : Fin m → LevQ Dw d.l₂ => if q = fun b => Submodule.Quotient.mk ((d.pd : 𝓞 E) • x b) then
        (Nat.card (Fin m → LevQ Dw d.l₂) : d.c₂.F) else 0) 1).1 k y₂
    have e₂ : v₂ = evR Xo c f y :=
      GlobalTheory.T.standardCover_shortValue_eq_thetaValue hC E H Dw l Xo c nab n d hd hn hn₂ m N a' x P _ hu₂ hP
        (fun b => (eq_mk_iff d hd (x b) _).1 rfl) k hk y y₂ hy v₂ _ hv₂
        ((GlobalTheory.thetaRule_exists_and_eval hC E H Dw l Xo c nab hn a' m x P hP).2 f hfr k y)
    have n₁ : d.eF (betaH (Dw := Dw) c Λ) ≠ 0 := (map_ne_zero _).2 b₁.1
    have n₂ : d.eF (betaH (Dw := Dw) c (blockLat Λ (unitLat E m))) ≠ 0 := (map_ne_zero _).2 b₂.1
    obtain ⟨hQ₂, hval⟩ := hprod a a' _ _ hP₁ hP₂
    have hv := (hval _ _ k y₂ _ _ _ ((Survey.BaseClassMove.shortValAt_beta _ _ _ _ _ _ n₁ _ _ _ _).1 hv₁) hv₂).2 rfl
    have hlin := shortVal_sum hC hn₂ hB.1 hB.2.2 hBL hQ₂ (fun x' => d.eF (cf x'))
      (fun x' q => d.eF (zetaM c ^ pairL (l := l) (Fin.append x0 fun b => qRep (x' b)) (fun b => levRep (q b)) * φ' q))
      _ (d.eF ζ)
      (sum_data d hd φ' ζ hφ x0 x) 1 y₂ _
      (fun x' => algebraMap d.c₂.F k (d.eF (betaH (Dw := Dw) c (blockLat Λ (unitLat E m)))) * u x') hv
      (fun x' => by
        rw [← map_blockPoly]
        exact (Survey.BaseClassMove.shortValAt_beta _ _ _ _ _ _ n₂ _ _ _ _).1 (hu x'))
    simp only [hk] at hlin
    let L := evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y
    have hL : ∀ f, L f = evR Xo c f y := fun _ => rfl
    have hm : evR Xo c (g * f) y = evR Xo c g y * evR Xo c f y := evalAt_mul _ _ g f y
    have eu' : ∀ x', evR Xo c (F x') y = evR d.Xo₂ d.c₂ d.cδ y₂ * u x' := eu
    rw [hm, ← hL (∑ x', _), map_sum, e₁, ← e₂]
    simp only [map_smul]
    simp only [hL, eu', Algebra.smul_def]
    have n₃ : algebraMap c.F k (betaH (Dw := Dw) c Λ) ≠ 0 := (map_ne_zero _).2 b₁.1
    have n₄ : algebraMap c.F k ζ ≠ 0 := (map_ne_zero _).2 hζ0
    refine mul_left_cancel₀ (mul_ne_zero n₄ n₃) ?_
    have e₃ : ∀ x', algebraMap c.F k ζ * algebraMap c.F k (betaH (Dw := Dw) c Λ) *
        (algebraMap c.F k (ζ' * ζ⁻¹ * cf x') * (evR d.Xo₂ d.c₂ d.cδ y₂ * u x')) = evR d.Xo₂ d.c₂ d.cδ y₂ *
        (algebraMap c.F k (cf x') * (algebraMap c.F k (betaH (Dw := Dw) c (blockLat Λ (unitLat E m))) * u x')) := by
      intro x'
      rw [eβ]
      simp only [map_mul, map_inv₀, map_one]
      field_simp
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun x' _ => e₃ x']
    rw [← Finset.mul_sum, hlin]
    ring
  rw [main]
  refine Submodule.sum_mem _ fun x' _ => ?_
  exact (Submodule.span (𝓞 c.F) _).smul_mem (⟨_, hcf x'⟩ : 𝓞 c.F) (Submodule.subset_span
    ⟨hFs x', _, N, _, _, hB.1, hB.2.1, hB.2.2, hBL, hadm x', hQ, hFr x'⟩)

end General

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

theorem short_mul_theta_mem_span : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (w wL : WeightFamilies.Wt D j), D.R.r ≤ w.n → (w.n = D.R.nV → wL.n = 0) → ∀ g ∈ T.sh j w, ∀ f ∈ T.th j wL, g * f ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j (WeightAlgebra.wadd w wL)) := by
  intro hC D T h j hj hS h1 hA w wL hr hV g hg f hf
  obtain ⟨s, hn⟩ := h.nabPin j hj
  obtain ⟨s₂, hn₂⟩ := hS.dNab j hj w.n
  obtain rfl : s = s₂ := starRing_eq _ _ fun a => (hn.1 a).trans (hn₂.1 a).symm
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
    have h1 := hj.1
    have h2 := hj.2
    have h3 := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have hr1 : 1 ≤ D.R.r := by
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]
    omega
  have hd := hS.dLev j hj w.n
  by_cases hpt : ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (_ : Algebra T.Q.c.F k),
      Nonempty (FrPt (T.Q.Xo j) T.Q.c k)
  swap
  · have e : g * f = 0 := GlobalTheory.ClassSumUnique.sec_eq_of_geometric
      (sec_mul _ _ _ _ _ _ hg.1 (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hn _ _ f hf))
      (Submodule.zero_mem _) fun k _ _ _ y => absurd ⟨k, _, ‹_›, _, ⟨y⟩⟩ hpt
    rw [e]
    exact Submodule.zero_mem _
  obtain ⟨k, _, _, _, ⟨y⟩⟩ := hpt
  obtain ⟨φ', e⟩ := h1.eq_withCoeff w.n (w.n + wL.n)
  obtain ⟨φ₀, e₀⟩ := h1 w.n
  have hA' : (T.dδ j w.n).l₂.A = 1 := by rw [e₀]; exact hA
  obtain ⟨ph, ψ, x₀, -, hp, ht⟩ := hS.dPhi j hj w.n hr
  have h2 := hS.dPhi j hj (w.n + wL.n) (hr.trans (Nat.le_add_right _ _))
  have h3 := hS.shTot j hj _ (w.n + wL.n) (dom_wtA (WeightAlgebra.wadd w wL))
  change g * f ∈ Submodule.span (𝓞 T.Q.c.F) (shortGen (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV
    (wtA (WeightAlgebra.wadd w wL)) (w.n + wL.n) (T.dδ j (w.n + wL.n)))
  rw [e] at h2 h3 ⊢
  rw [wtA_wadd] at h3 ⊢
  obtain ⟨ph', ψ', x₀', -, hp', ht'⟩ := h2
  letI : Algebra (T.dδ j w.n).c₂.F k :=
    ((algebraMap T.Q.c.F k).comp ((T.dδ j w.n).eF.symm : (T.dδ j w.n).c₂.F →+* T.Q.c.F)).toAlgebra
  obtain ⟨y₂, -⟩ := hd.2.2.2.2.2.2.1 k (fun t => by
    show algebraMap T.Q.c.F k ((T.dδ j w.n).eF.symm ((T.dδ j w.n).eF t)) = _
    rw [AlgEquiv.symm_apply_apply]) y
  obtain rfl : ψ = ψ' := GlobalTheory.CoverCharacter.psi_unique _ _ _ _ _ _ _ (T.dδ j w.n) (hpq ▸ hr1) hd hA' k ⟨y₂⟩ ψ ψ' ht ht'
  obtain ⟨ζ, hζ, hφ⟩ := GlobalTheory.MoreColumns.coeff_more_columns _ _ _ _ _ _ _ _ (T.dδ j w.n) φ' hd (hpq ▸ hr) ψ ph x₀ ph' x₀'
    hp hp'
  exact mul_mem_span hC hn (T.dδ j w.n) hd hn₂ φ' ζ hζ hφ (badN D) D.R.nV hV
    (fun k Λ => hS.beta j hj k (h.kPsi j hj) Λ) _ _ h3 hg hf

end GlobalTheory.ShortTimesTheta
end
end

section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem productsShort_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), LawsSh T → OneCover T j → (T.dδ j 0).l₂.A = 1 → ∀ (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ka.n = D.R.nV → ProductsShort (recPJ h j hj) ka wL wF Tn :=
  productsShort_of_oneFactor GlobalTheory.ShortTimesTheta.short_mul_theta_mem_span

end GlobalTheory.FormTies
end
