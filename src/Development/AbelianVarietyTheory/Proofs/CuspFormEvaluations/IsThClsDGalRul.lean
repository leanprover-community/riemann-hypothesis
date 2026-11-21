import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AdmissibleColumnsLeAndHarmonicMapCover
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjugateSectionValuesSemilinearStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.XLaterHarmonicNotMemSpan
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelFourierTransformAutAndHomogeneous

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalTw

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

theorem isNab_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → IsNab Xo c (fun {S} _ _ y k F α => (nab (twPt h y) k F α).val) := by
  intro E _ _ _ H Dw l Xo c ta h _ nab hn
  refine ⟨hn.1, fun S _ _ iQ y => ?_⟩
  letI : Algebra ℚ (Tw ta S) := iQ
  obtain ⟨C, h1, h2⟩ := hn.2 (Tw ta S) (twPt h y)
  exact ⟨⟨C.d, C.B, C.uvec, C.x, C.e, C.wP, C.h,
    ⟨C.chart.1, C.chart.2, C.chart.3, C.chart.4, C.chart.5, C.chart.6⟩,
    ⟨C.frame.1, C.frame.2, C.frame.3, C.frame.4, C.frame.5⟩, C.prim, C.gauge, C.rig0⟩, h1, h2⟩

end GlobalTheory.GalTw
end
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

theorem colSum_eq_of_isNab (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (nab nab' : NabV Xo c) (h : IsNab Xo c nab) (h' : IsNab Xo c nab') {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (K : ℤ) (k : ℕ) (hK : K = (k : ℤ))
    (G : Fin n → LB.Sec (ReciprocityTheory.ChartRestriction.G.Out.LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x))) :
    ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (G b) (colOf m b) =
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab' y K (G b) (colOf m b) := by
  subst hK
  exact GlobalTheory.NabUniqCompare.thExprUniqSt_iff_top.1 (Formalism.MainNotions.ModuliIntegralCharts.H1.thExprUniq_of_chartIndep2 hC) E H Dw l Xo c
    nab nab' h h' S y k n G P
    ⟨(GlobalTheory.NabUniqCompare.isHarmonic_iff_cmType c P).2 hP.1, hP.2.1, a, hP.2.2⟩

theorem coeffAutFixesCMConjugatesAndBase_symm {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {l : Level H} {c : Coeff l} {ta : c.F ≃+* c.F} (h : Fixes c ta) : Fixes c ta.symm :=
  ⟨fun τ a => (ta.symm_apply_eq).2 (h.emb τ a).symm, fun a => (ta.symm_apply_eq).2 (h.base a).symm⟩

theorem algebraMap_tw_symm {K : Type} [Field K] (ta : K ≃+* K) (S : Type) [CommRing S] [Algebra K S] (x : K) :
    (algebraMap K (Tw ta.symm S) (ta x)).val = algebraMap K S x := by
  change algebraMap K S (ta.symm (ta x)) = _
  rw [RingEquiv.symm_apply_apply]

theorem shortValAt_conj : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  intro hC E _ _ _ H Dw l Xo c ta h _ nab hnab n a P hP w Λ b N S _ _ y v hv
  obtain ⟨S', i1, i2, φ, y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, hv⟩ := hv
  have h' : Fixes c ta.symm := coeffAutFixesCMConjugatesAndBase_symm h
  have hnab' := GlobalTheory.GalTw.isNab_twist E H Dw l Xo c ta.symm h' nab hnab
  let φ' : S →ₐ[c.F] Tw ta.symm S' :=
    { toRingHom := φ.toRingHom
      commutes' := fun x => by
        have := φ.commutes (ta.symm x)
        change φ (algebraMap c.F S (ta (ta.symm x))) = _ at this
        rw [RingEquiv.apply_symm_apply] at this
        exact this }
  have hinj : Function.Injective (ta : c.F →+* c.F) := ta.injective
  have hsupp : (MvPolynomial.map (ta : c.F →+* c.F) P).support = P.support :=
    MvPolynomial.support_map_of_injective P hinj
  have hdeg : (MvPolynomial.map (ta : c.F →+* c.F) P).totalDegree = P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [hsupp]
  refine ⟨Tw ta.symm S', inferInstance, inferInstance, φ', twPt h' y', z, tp, F, hff, hmap, hz, hgeo, htp, hF, ?_⟩
  have e1 : (ta b)⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ *
        ((N : c.F) ^ P.totalDegree)⁻¹ = ta (b⁻¹ * ((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
        ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) := by
    simp only [map_mul, map_inv₀, map_pow, map_natCast]
  rw [hsupp, hdeg, e1]
  refine hv.trans ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine finsum_congr fun q => ?_
  refine congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (colSum_eq_of_isNab hC Xo c _ _ hnab hnab' a P hP S' y' _ (N ^ 2) (Nat.cast_pow N 2).symm (F q i)).trans ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map]
  exact congrArg₂ (fun s t : S' => s * t) (algebraMap_tw_symm ta S' _).symm rfl

end GlobalTheory.GalTw
end

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortSeriesValue_twisted_eq_conjugate_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b : c.F) (N : ℕ) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : Tw ta S), ShortValAt Xo c nab w Λ b N P (twPt h y) v → ShortValAt Xo c nab (fun q => ta (w q)) Λ (ta b) N (MvPolynomial.map (ta : c.F →+* c.F) P) y v.val := by
  atlas_forward_decl GlobalTheory.GalTw.shortValAt_conj
end

section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_fourier_transform_aut_and_homogeneous : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ), (∀ ta : c.F ≃+* c.F, (∃ a a' : ℕ, ta (zetaM c) = zetaM c ^ a ∧ a * a' ≡ 1 [MOD l.M]) ∧ ∀ a a' : ℕ, ta (zetaM c) = zetaM c ^ a → a * a' ≡ 1 [MOD l.M] → ∀ (φ : (Fin n → LevQc Dw l) → c.F) (q : Fin n → LevQ Dw l), ta (phiHat c φ q) = phiHat c (fun x => ta (φ (a' • x))) q) ∧ (∀ (u : c.F) (φ : (Fin n → LevQc Dw l) → c.F) q, phiHat c (fun x => u * φ x) q = u * phiHat c φ q) ∧ ∀ (nab : NabV Xo c) (w : (Fin n → LevQ Dw l) → c.F) (Λ : GenLat E n) (b u : c.F) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S), ShortValAt Xo c nab w Λ b N P y v → ShortValAt Xo c nab (fun q => u * w q) Λ b N P y (algebraMap c.F S u * v) := by
  first | exact @GlobalTheory.GalTw.phiHat_aut_and_mul | exact GlobalTheory.GalTw.phiHat_aut_and_mul | (intros; apply GlobalTheory.GalTw.phiHat_aut_and_mul <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GalTw

namespace GlobalTheory.GalTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem covAut_eF {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F) (a : c.F) :
    covAut d ta (d.eF a) = d.eF (ta a) := by
  show d.eF (ta (d.eF.symm (d.eF a))) = _
  rw [AlgEquiv.symm_apply_apply]

theorem thLa_conj (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {n : ℕ} (d : DeltaDat Xo c n) (ta : c.F ≃+* c.F)
    (h₂ : Fixes d.c₂ (covAut d ta)) [StarRing (𝓞 E)] (hN : IsNab d.Xo₂ d.c₂ d.nab₂) (u : c.F) (hu : u ≠ 0)
    (w w' : (Fin n → LevQ Dw d.l₂) → c.F) (hw : ∀ q, ta (w q) = u * w' q) (La : GenLat E n) (N : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)))
    (k : Type) [CommRing k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k) (v : Tw (covAut d ta) k)
    (hv : thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
      (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (twPt h₂ y₂) v) :
    thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w' q)) La N
      (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (MvPolynomial.map (ta : c.F →+* c.F) P)) y₂
      (algebraMap d.c₂.F k (d.eF u⁻¹) * v.val) := by
  have h1 := GlobalTheory.T.shortSeriesValue_twisted_eq_conjugate_value hC E H Dw d.l₂ d.Xo₂ d.c₂ (covAut d ta) h₂ d.nab₂ hN n a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ La 1 N k y₂ v hv
  have h3 := (GlobalTheory.T.level_fourier_transform_aut_and_homogeneous E H Dw d.l₂ d.Xo₂ d.c₂ n).2.2 d.nab₂ _ La _ (d.eF u⁻¹) N _ k y₂ _ h1
  have e1 : (fun q => d.eF u⁻¹ * covAut d ta (d.eF (w q))) = fun q => d.eF (w' q) := by
    funext q
    rw [covAut_eF, hw, ← map_mul, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  have e2 : MvPolynomial.map (covAut d ta : d.c₂.F →+* d.c₂.F) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (MvPolynomial.map (ta : c.F →+* c.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => covAut_eF d ta a)
  rw [e1, e2, map_one] at h3
  exact h3

theorem isThClsD_galRul : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (ta : c.F ≃+* c.F) (h : Fixes c ta), ∀ (n : ℕ) (d : DeltaDat Xo c n) (h₂ : Fixes d.c₂ (covAut d ta)), (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (cx : Rul d.Xo₂ d.c₂) (ka u : c.F), ka ≠ 0 → u ≠ 0 → (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ (galRul h₂ d.cδ) y₂ = algebraMap d.c₂.F k (d.eF ka) * evR d.Xo₂ d.c₂ cx y₂) → ∀ (Cl : Type) [Fintype Cl] (w w' : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (a : (E →+* ℂ) × ℕ → ℕ), (∀ v, io v ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))) → (∀ k q, ta (w k q) = u * w' k q) → ∀ x x' : Cl → Vs, (∀ k, io (x' k) = MvPolynomial.map (ta : c.F →+* c.F) (io (x k))) → ∀ (m : ℕ), ∀ f ∈ sec Xo c a m, IsThClsD Xo c d w La Nc gam vol ep io x f → (ka * u)⁻¹ • galRul h f ∈ sec Xo c a m ∧ IsThClsD Xo c { d with cδ := cx } w' La Nc gam (ta vol) (fun k => ta (ep k)) io x' ((ka * u)⁻¹ • galRul h f) := by
  intro hC E _ _ _ H Dw l Xo c ta h n d h₂ hN hδ cx ka u hka hu hcx Cl _ w w' La Nc gam vol ep Vs _ _ io a hio hw
    x x' hx m f hf hT
  obtain ⟨_, hN⟩ := hN
  obtain ⟨hs, hv⟩ := (GlobalTheory.T.conjugateSection_values_semilinear E H Dw l Xo c ta h).1 a m f hf
  have hv₂ := ((GlobalTheory.T.conjugateSection_values_semilinear E H Dw d.l₂ d.Xo₂ d.c₂ (covAut d ta) h₂).1 0 0 d.cδ hδ).2
  refine ⟨Submodule.smul_mem _ _ hs, ?_⟩
  intro k _ _ A A₂ hk y y₂ hy
  letI A₂' : Algebra d.c₂.F k := A₂
  have hk' : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a := hk
  obtain ⟨vc, hvc, he⟩ := @hT k _ _ (inferInstance : Algebra c.F (Tw ta k))
    (inferInstance : Algebra d.c₂.F (Tw (covAut d ta) k))
    (fun a => by
      show algebraMap d.c₂.F k (covAut d ta (d.eF a)) = algebraMap c.F k (ta a)
      rw [covAut_eF, hk'])
    (twPt h y) (twPt h₂ y₂) hy
  refine ⟨fun cl => algebraMap d.c₂.F k (d.eF u⁻¹) * vc cl, fun cl => ?_, ?_⟩
  · rw [hx]
    exact thLa_conj hC d ta h₂ hN u hu (w cl) (w' cl) (hw cl) (La cl) (Nc cl) a _ (hio _) k y₂ (vc cl) (hvc cl)
  · have e0 : evR Xo c ((ka * u)⁻¹ • galRul h f) y = algebraMap c.F k (ka * u)⁻¹ * evR Xo c (galRul h f) y :=
      evalAt_smul _ _ _ _ y
    have he' : evR Xo c (galRul h f) y = evR d.Xo₂ d.c₂ (galRul h₂ d.cδ) y₂ *
        ∑ cl, algebraMap c.F k (ta (vol * ((gam cl : c.F))⁻¹ * ep cl)) * vc cl := by
      rw [hv k y, hv₂ k y₂]
      exact he
    show _ = evR d.Xo₂ d.c₂ cx y₂ * _
    rw [e0, he', hcx k y₂, hk', hk']
    have hka' : algebraMap c.F k ka ≠ 0 := (map_ne_zero _).2 hka
    simp only [map_mul, map_inv₀, map_natCast, mul_inv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun cl _ => ?_
    field_simp

end GlobalTheory.GalTw
end
end
