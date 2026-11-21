import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaConstantMulOfCoprimeEllipticPolynomials
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjGLOfCharpolyEqOfSeparable
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.PClsOnto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.FibL

section Generic

variable {G : Type} [Group G]

def twR (θ : G →* G) (x y : G) : Prop := ∃ g, y = g⁻¹ * x * θ g

theorem twR_equiv (θ : G →* G) : Equivalence (twR θ) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk (twR θ) x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ twR θ x y :=
  ⟨fun h => (twR_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem locEl_eventually_mem (n : ℕ) (δ : GL (Fin n) E) :
    ∀ᶠ w : Pl E in cofinite, locEl n w δ ∈ GlobalTheory.LFun.KGL w n := by
  filter_upwards [UnitStable.eventually_mem_KGL δ, UnitStable.eventually_mem_KGL (δ * thE E n δ)] with w h1 h2
  unfold locEl
  split_ifs
  · exact h2
  · exact h1

end CompanionTheory.Rg.BcB.G3.FibL

namespace CompanionTheory.Rg.BcB.G3.ParamLP

theorem tw_symm {G : Type} [Group G] (θ : G →* G) {x y : G} (h : ∃ g, x = g⁻¹ * y * θ g) :
    ∃ g, y = g⁻¹ * x * θ g := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  simp only [inv_inv, map_inv]
  group

theorem tw_trans {G : Type} [Group G] (θ : G →* G) {x y z : G} (h₁ : ∃ g, x = g⁻¹ * y * θ g)
    (h₂ : ∃ g, y = g⁻¹ * z * θ g) : ∃ g, x = g⁻¹ * z * θ g := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  refine ⟨h * g, ?_⟩
  simp only [map_mul]
  group

theorem exists_over {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 F) = v := by
  have := v.isPrime
  obtain ⟨Q, hQ, hl⟩ := (Ideal.nonempty_primesOver v.asIdeal (S := 𝓞 K)).some
  exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem finite_over {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (v : HeightOneSpectrum (𝓞 F)) : {u : HeightOneSpectrum (𝓞 K) | u.under (𝓞 F) = v}.Finite := by
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := fun u : HeightOneSpectrum (𝓞 K) => u.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  intro u hu
  change u.under (𝓞 F) = v at hu
  refine ⟨u.isPrime, ⟨?_⟩⟩
  rw [← hu]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem thE_thE (n : ℕ) (g : GL (Fin n) E) : thE E n (thE E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ (fun x => IsCMField.complexConj_apply_apply E x) g

theorem nrm_tw (n : ℕ) (z g : GL (Fin n) E) :
    (g⁻¹ * z * thE E n g) * thE E n (g⁻¹ * z * thE E n g) = g⁻¹ * (z * thE E n z) * g := by
  rw [map_mul, map_mul, map_inv, thE_thE]
  group

theorem locEl_tw (hU : Unr E) (n : ℕ) (w : Pl E) (z g : GL (Fin n) E) :
    ∃ h, locEl n w (g⁻¹ * z * thE E n g) = h⁻¹ * locEl n w z * thL n w h := by
  refine ⟨GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g, ?_⟩
  unfold locEl thL
  split_ifs with hs
  · rw [nrm_tw, map_mul, map_mul, map_inv, MonoidHom.id_apply]
  · have hm : GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (thE E n g) =
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) g) :=
      GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (((GlobalTheory.T.placeConjugation_properties_cmField E hU w).2.2.2.1 hs).1 x).symm) g
    rw [map_mul, map_mul, map_inv, hm]

theorem locEl_rel (hU : Unr E) (n : ℕ) (w : Pl E) {z z' : GL (Fin n) E} (h : ∃ g, z' = g⁻¹ * z * thE E n g)
    (yw : GLw n w) :
    (∃ g, locEl n w z = g⁻¹ * yw * thL n w g) ↔ ∃ g, locEl n w z' = g⁻¹ * yw * thL n w g := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨k, hk⟩ := locEl_tw hU n w z g
  rw [hk]
  constructor
  · intro hz
    exact tw_trans _ ⟨k, rfl⟩ hz
  · intro hz
    exact tw_trans _ (tw_symm _ ⟨k, rfl⟩) hz

theorem param_main (h1 : SkewEx) (h2 : Struct) (h3 : QuadField) (h4 : LocDict) (h5 : ClsNorm) (h6 : ClsOnto)
    (h7 : ClsEq) (h8 : LocGood) : Param := by
  intro E _ _ _ hU n S hS P hP y hy hyK
  obtain ⟨s, d, hs0, hsc, hsd⟩ := h1 E
  obtain ⟨δ, hδ⟩ := GlobalTheory.BCT.KapMul.exists_norm E hP
  have hPδ : (δ * thE E n δ).val.charpoly ∈ Ell E n := by rw [hδ]; exact hP
  have hsep : (δ * thE E n δ).val.charpoly.Separable := hPδ.2.2.1
  obtain ⟨ι, _, K, _, _, _, ρ, hcard, hreal, hsum, hfr⟩ := h2 E s d hs0 hsc hsd n δ hPδ
  choose hinf L fL nfL aL qL hLc hglob hloc using fun i => h3 E s d hs0 hsc hsd (K i) (hreal i)
  have hinv : ∀ x, (IsCMField.complexConj E).toRingEquiv.toRingHom
      ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x := fun x => IsCMField.complexConj_apply_apply E x
  have hyδ : ∀ w, (nrmL n w (y w)).val.charpoly = atPl w (δ * thE E n δ).val.charpoly := fun w => by
    rw [hδ]; exact hy w
  choose X hX using fun w => h4 E hU s d hs0 hsc hsd n δ hsep ι K ρ hfr w (y w) (hyδ w)
  have hW : ∀ i (u : HeightOneSpectrum (𝓞 (K i))), ∃ w ∈ S,
      w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E)) := by
    intro i u
    obtain ⟨w0, hw0⟩ := exists_over (K := E) (u.under (𝓞 (maximalRealSubfield E)))
    obtain ⟨w, ⟨hwS, hw⟩, -⟩ := hS w0
    exact ⟨w, hwS, hw.trans hw0⟩
  choose W hWS hWu using hW
  let x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i) := fun i u => X (W i u) i ⟨u, (hWu i u).symm⟩
  have hxX : ∀ i (w : Pl E) (u : {u : HeightOneSpectrum (𝓞 (K i)) //
      u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}), w ∈ S → x i u.1 = X w i u := by
    intro i w u hw
    have e : W i u.1 = w := (hS w).unique ⟨hWS i u.1, (hWu i u.1).trans u.2⟩ ⟨hw, rfl⟩
    have key : ∀ (w1 : Pl E) (_ : w1 = w) (p : u.1.under (𝓞 (maximalRealSubfield E)) =
        w1.under (𝓞 (maximalRealSubfield E))), X w1 i ⟨u.1, p⟩ = X w i u := by
      rintro w1 rfl p; rfl
    exact key _ e _
  let ev : ∀ i, (∀ j, K j)ˣ →* (K i)ˣ := fun i => Units.map (Pi.evalMonoidHom K i)
  have hloc' : ∀ (t : (∀ i, K i)ˣ) (w : Pl E), w ∈ S →
      ((∃ g, locEl n w (pt δ ρ.toRingHom t) = g⁻¹ * y w * thL n w g) ↔
      ∀ i (u : {u : HeightOneSpectrum (𝓞 (K i)) //
        u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))}),
        x i u.1 / GlobalTheory.QuadSymbol.finDiag (K i) (ev i t) u.1 ∈
          GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.1.adicCompletion (K i))) := by
    intro t w hw
    rw [hX w t]
    refine forall_congr' fun i => forall_congr' fun u => ?_
    rw [hxX i w u hw, hloc i u.1]
    have hne : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ j, K j) i) ≠ 0 :=
      (_root_.map_ne_zero _).2 (ev i t).ne_zero
    have hv : ((X w i u / GlobalTheory.QuadSymbol.finDiag (K i) (ev i t) u.1 : (u.1.adicCompletion (K i))ˣ) :
        u.1.adicCompletion (K i)) = (X w i u : u.1.adicCompletion (K i)) /
          algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ j, K j) i) := by
      rw [Units.val_div_eq_div_val]; rfl
    rw [hv]
    constructor
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, by rw [h, mul_div_cancel_left₀ _ hne]⟩
    · rintro ⟨a, b, h⟩
      exact ⟨a, b, by rw [div_eq_iff hne] at h; rw [h, mul_comm]⟩

  have hev : ∀ᶠ w : Pl E in cofinite, ∃ g, locEl n w (pt δ ρ.toRingHom 1) = g⁻¹ * y w * thL n w g := by
    filter_upwards [h8 E hU n P hP, hyK, FibL.locEl_eventually_mem n δ] with w hw hyw hδw
    obtain ⟨g, hg⟩ := (hw (locEl n w δ) hδw (by rw [ThBasic.charpoly_nrmL hU, hδ])).2.2 (y w) hyw (hy w)
    refine ⟨g⁻¹, ?_⟩
    rw [hg, show pt δ ρ.toRingHom 1 = δ by simp [pt]]
    simp only [map_inv, inv_inv]
    group
  have hAN : ∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i) := by
    intro i
    have hbad := Filter.eventually_cofinite.1 hev
    refine (hbad.biUnion fun w _ =>
      finite_over (F := maximalRealSubfield E) (K := K i) (w.under (𝓞 (maximalRealSubfield E)))).subset ?_
    intro u hu
    have hWbad : W i u ∈ {w : Pl E | ¬ ∃ g, locEl n w (pt δ ρ.toRingHom 1) = g⁻¹ * y w * thL n w g} := by
      intro hgood
      apply hu
      have h0 := (hloc' 1 (W i u) (hWS i u)).1 hgood i ⟨u, (hWu i u).symm⟩
      have h1 : GlobalTheory.QuadSymbol.finDiag (K i) (ev i 1) u = 1 := by
        rw [map_one]
        exact map_one (GlobalTheory.QuadSymbol.toUnits (K i) (u.adicCompletion (K i)))
      rw [h1, div_one] at h0
      exact h0
    exact Set.mem_biUnion hWbad (hWu i u).symm
  have hC : ∀ c : {c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧
      ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g},
      ∃ (t : (∀ i, K i)ˣ) (g : GL (Fin n) E), c.1.rep = g⁻¹ * pt δ ρ.toRingHom t * thE E n g :=
    fun c => h6 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr hsep c.1.rep (c.2.1.trans hδ.symm)
  choose tc gc htc using hC
  have hcond : ∀ c i u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) (ev i (tc c)) u ∈
      GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i)) := by
    intro c i u
    have hl : ∃ g, locEl n (W i u) (pt δ ρ.toRingHom (tc c)) = g⁻¹ * y (W i u) * thL n (W i u) g :=
      (locEl_rel hU n (W i u) ⟨gc c, htc c⟩ (y _)).2 (c.2.2 _ (hWS i u))
    exact (hloc' (tc c) (W i u) (hWS i u)).1 hl i ⟨u, (hWu i u).symm⟩
  refine ⟨ι, inferInstance, K, L, inferInstance, inferInstance, fL, nfL, aL, qL, x, ?_, hreal, hLc, hAN, ?_,
    ⟨Equiv.ofBijective (fun c i => ⟨QuotientGroup.mk (ev i (tc c)), ev i (tc c), rfl, hcond c i⟩) ⟨?_, ?_⟩⟩⟩
  · rw [hcard, hδ]
  · rw [Finset.sum_congr rfl (fun i _ => hinf i), ← Finset.sum_mul, hsum]
  · intro c c' hcc
    have hq : ∀ i, (ev i (tc c))⁻¹ * ev i (tc c') ∈ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) := fun i =>
      QuotientGroup.eq.1 (congrArg (fun f => (f i).1) hcc)
    choose a b hab using fun i => (hglob i _).1 (hq i)
    have hrel : ∃ g, pt δ ρ.toRingHom (tc c) = g⁻¹ * pt δ ρ.toRingHom (tc c') * thE E n g := by
      refine (h7 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr (tc c') (tc c)).2 ⟨a, b, funext fun i => ?_⟩
      have hi := hab i
      rw [Units.val_mul, Units.val_inv_eq_inv_val] at hi
      change (tc c' : ∀ j, K j) i = (tc c : ∀ j, K j) i * (a i ^ 2 - algebraMap (maximalRealSubfield E) (K i) d * b i ^ 2)
      rw [← hi]
      change (tc c' : ∀ j, K j) i = (tc c : ∀ j, K j) i * (((tc c : ∀ j, K j) i)⁻¹ * (tc c' : ∀ j, K j) i)
      rw [← mul_assoc, mul_inv_cancel₀ (show (tc c : ∀ j, K j) i ≠ 0 from (ev i (tc c)).ne_zero), one_mul]
    apply Subtype.ext
    rw [← FibL.cls_rep _ c.1, ← FibL.cls_rep _ c'.1, FibL.cls_eq_iff]
    have e := FibL.twR_equiv (thE E n)
    exact e.trans (e.symm ⟨gc c, htc c⟩) (e.trans (e.symm hrel) ⟨gc c', htc c'⟩)
  · intro f
    choose T hT hTc using fun i => (f i).2
    let Tu : (∀ i, K i)ˣ := ⟨fun i => (T i : K i), fun i => ((T i)⁻¹ : (K i)ˣ),
      funext fun i => (T i).mul_inv, funext fun i => (T i).inv_mul⟩
    have hTu : ∀ i, ev i Tu = T i := fun i => Units.ext rfl
    obtain ⟨g0, hg0⟩ : FibL.twR (thE E n) (pt δ ρ.toRingHom Tu)
        (FibL.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep :=
      (FibL.cls_eq_iff _ _ _).1 (FibL.cls_rep _ _).symm
    have hmem : ((FibL.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep *
        thE E n (FibL.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep).val.charpoly = P ∧
        ∀ w ∈ S, ∃ g, locEl n w (FibL.cls (thE E n) (pt δ ρ.toRingHom Tu)).rep = g⁻¹ * y w * thL n w g := by
      refine ⟨?_, fun w hw => ?_⟩
      · rw [hg0, nrm_tw, show pt δ ρ.toRingHom Tu * thE E n (pt δ ρ.toRingHom Tu) = δ * thE E n δ from
          h5 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr Tu, ← hδ, Units.val_mul, Units.val_mul,
          Matrix.coe_units_inv, Matrix.charpoly_units_conj']
      · refine (locEl_rel hU n w ⟨g0, hg0⟩ (y w)).1 ((hloc' Tu w hw).2 fun i u => ?_)
        rw [hTu]
        exact hTc i u.1
    refine ⟨⟨FibL.cls (thE E n) (pt δ ρ.toRingHom Tu), hmem⟩, funext fun i => Subtype.ext ?_⟩
    have hrel : ∃ g, pt δ ρ.toRingHom (tc ⟨_, hmem⟩) = g⁻¹ * pt δ ρ.toRingHom Tu * thE E n g := by
      have e := FibL.twR_equiv (thE E n)
      exact e.trans ⟨g0, hg0⟩ (e.symm ⟨gc ⟨_, hmem⟩, htc ⟨_, hmem⟩⟩)
    obtain ⟨uu, vv, huv⟩ := (h7 E n _ hinv δ s hs0 hsc _ _ ρ.toRingHom hfr Tu (tc ⟨_, hmem⟩)).1 hrel
    change QuotientGroup.mk (ev i (tc ⟨_, hmem⟩)) = (f i).1
    rw [hT i, ← hTu i]
    refine QuotientGroup.eq.2 ((hglob i _).2 ⟨uu i, vv i, ?_⟩)
    have hi := congrFun huv i
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    change ((tc ⟨_, hmem⟩ : ∀ j, K j) i)⁻¹ * (Tu : ∀ j, K j) i = _
    rw [hi]
    change ((tc ⟨_, hmem⟩ : ∀ j, K j) i)⁻¹ * ((tc ⟨_, hmem⟩ : ∀ j, K j) i *
      (uu i ^ 2 - algebraMap (maximalRealSubfield E) (K i) d * vv i ^ 2)) = _
    rw [← mul_assoc, inv_mul_cancel₀ (show (tc ⟨_, hmem⟩ : ∀ j, K j) i ≠ 0 from (ev i (tc ⟨_, hmem⟩)).ne_zero), one_mul]

end CompanionTheory.Rg.BcB.G3.ParamLP

namespace CompanionTheory.Rg.BcB.G3

theorem param_pfL (h1 : SkewEx) (h2 : Struct) (h3 : QuadField) (h4 : LocDict) (h5 : ClsNorm) (h6 : ClsOnto)
    (h7 : ClsEq) (h8 : LocGood) : Param :=
  ParamLP.param_main h1 h2 h3 h4 h5 h6 h7 h8

end CompanionTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3

theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  have hne := IsCMField.complexConj_ne_one E
  have hz : ∃ z : E, IsCMField.complexConj E z ≠ z := by
    by_contra h
    push_neg at h
    exact hne (AlgEquiv.ext fun x => by simpa using h x)
  obtain ⟨z, hz⟩ := hz
  set s : E := z - IsCMField.complexConj E z with hs
  have hs0 : s ≠ 0 := fun h => hz (sub_eq_zero.1 h).symm
  have hcs : IsCMField.complexConj E s = -s := by
    rw [hs, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hmem : s ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hcs, neg_sq]
  exact ⟨s, ⟨s ^ 2, hmem⟩, hs0, hcs, rfl⟩

end CompanionTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.StructP

section Fac

variable {E : Type} [Field E]

abbrev Fac (P : E[X]) : Type := {Q // Q ∈ (UniqueFactorizationMonoid.normalizedFactors P).toFinset}

theorem fac_mem {P : E[X]} (Q : Fac P) : Q.1 ∈ UniqueFactorizationMonoid.normalizedFactors P :=
  Multiset.mem_toFinset.1 Q.2

theorem fac_irr {P : E[X]} (Q : Fac P) : Irreducible Q.1 :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (fac_mem Q)

instance factIrr {P : E[X]} (Q : Fac P) : Fact (Irreducible Q.1) := ⟨fac_irr Q⟩

theorem fac_monic {P : E[X]} (Q : Fac P) : Q.1.Monic := by
  have h := UniqueFactorizationMonoid.normalize_normalized_factor _ (fac_mem Q)
  rw [← h]
  exact Polynomial.monic_normalize (fac_irr Q).ne_zero

theorem fac_dvd {P : E[X]} (Q : Fac P) : Q.1 ∣ P :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (fac_mem Q)

theorem fac_coprime (P : E[X]) : Pairwise (Function.onFun IsCoprime fun Q : Fac P => Q.1) := by
  intro Q Q' hne
  refine (Irreducible.coprime_iff_not_dvd (fac_irr Q)).2 fun hd => hne ?_
  exact Subtype.ext (Polynomial.eq_of_monic_of_associated (fac_monic Q) (fac_monic Q')
    ((fac_irr Q).associated_of_dvd (fac_irr Q') hd))

theorem nodup_fac {P : E[X]} (hP : P.Separable) : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
  (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP.ne_zero).1 hP.squarefree

theorem prod_fac {P : E[X]} (hm : P.Monic) (hP : P.Separable) : ∏ Q : Fac P, Q.1 = P := by
  rw [Finset.prod_coe_sort (UniqueFactorizationMonoid.normalizedFactors P).toFinset (fun Q => Q),
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_fac hP).dedup, Multiset.map_id']
  have hmon : (UniqueFactorizationMonoid.normalizedFactors P).prod.Monic := by
    simpa using Polynomial.monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors P) (fun Q => Q)
      (fun Q hQ => fac_monic (⟨Q, Multiset.mem_toFinset.2 hQ⟩ : Fac P))
  exact Polynomial.eq_of_monic_of_associated hmon hm (UniqueFactorizationMonoid.prod_normalizedFactors hP.ne_zero)

theorem card_fac {P : E[X]} (hP : P.Separable) : Fintype.card (Fac P) = nfac P := by
  rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_fac hP)]
  rfl

theorem fac_roots {P : E[X]} (hm : P.Monic) (hr : ∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) (Q : Fac P) :
    ∀ τ : E →+* ℂ, ∀ z ∈ (Q.1.map τ).roots, ‖z‖ = 1 := fun τ z hz =>
  hr τ z (Multiset.mem_of_le (Polynomial.roots.le_of_dvd (hm.map τ).ne_zero (Polynomial.map_dvd τ (fac_dvd Q))) hz)

theorem exists_rep (P : E[X]) (z : ∀ Q : Fac P, AdjoinRoot Q.1) :
    ∃ f : E[X], ∀ Q : Fac P, AdjoinRoot.mk Q.1 f = z Q := by
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : Fac P => (Ideal.span {Q.1} : Ideal E[X])) := by
    intro Q Q' h
    exact (Ideal.isCoprime_span_singleton_iff _ _).2 (fac_coprime P h)
  obtain ⟨x, hx⟩ := (Ideal.quotientInfRingEquivPiQuotient _ hcop).surjective z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨f, fun Q => congrFun hx Q⟩

end Fac

section Ev

variable {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E)

theorem aeval_eq_zero_iff (hs : N.charpoly.Separable) (f : E[X]) :
    aeval N f = 0 ↔ ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 f = 0 := by
  constructor
  · intro h Q
    exact AdjoinRoot.mk_eq_zero.2 ((fac_dvd Q).trans (GlobalTheory.ClassParam.charpoly_dvd_of_aeval N hs f h))
  · intro h
    have hd : ∏ Q : Fac N.charpoly, Q.1 ∣ f :=
      Fintype.prod_dvd_of_coprime (fac_coprime _) fun Q => AdjoinRoot.mk_eq_zero.1 (h Q)
    rw [prod_fac (Matrix.charpoly_monic N) hs] at hd
    obtain ⟨k, rfl⟩ := hd
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]

theorem aeval_eq_iff (hs : N.charpoly.Separable) (f g : E[X]) :
    aeval N f = aeval N g ↔ ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 g := by
  rw [← sub_eq_zero, ← map_sub, aeval_eq_zero_iff N hs]
  simp only [map_sub, sub_eq_zero]

variable {F : Type} [Field F] [Algebra F E] {K : Fac N.charpoly → Type} [∀ Q, Field (K Q)] [∀ Q, Algebra F (K Q)]
  (j : ∀ Q : Fac N.charpoly, K Q →+* AdjoinRoot Q.1)

def repOf (a : ∀ Q, K Q) : E[X] := (exists_rep N.charpoly fun Q => j Q (a Q)).choose

theorem repOf_spec (a : ∀ Q, K Q) (Q : Fac N.charpoly) : AdjoinRoot.mk Q.1 (repOf N j a) = j Q (a Q) :=
  (exists_rep N.charpoly fun Q => j Q (a Q)).choose_spec Q

def rhoFun (a : ∀ Q, K Q) : Matrix (Fin n) (Fin n) E := aeval N (repOf N j a)

theorem rhoFun_eq (hs : N.charpoly.Separable) (a : ∀ Q, K Q) (f : E[X])
    (hf : ∀ Q, AdjoinRoot.mk Q.1 f = j Q (a Q)) : rhoFun N j a = aeval N f :=
  (aeval_eq_iff N hs _ _).2 fun Q => (repOf_spec N j a Q).trans (hf Q).symm

def rho (hs : N.charpoly.Separable)
    (hj : ∀ Q x, j Q (algebraMap F (K Q) x) = AdjoinRoot.of Q.1 (algebraMap F E x)) :
    (∀ Q, K Q) →ₐ[F] Matrix (Fin n) (Fin n) E where
  toFun := rhoFun N j
  map_one' := by
    show rhoFun N j 1 = 1
    rw [rhoFun_eq N j hs 1 1 (fun Q => by rw [map_one, Pi.one_apply, map_one]), map_one]
  map_mul' a b := by
    show rhoFun N j (a * b) = rhoFun N j a * rhoFun N j b
    rw [rhoFun_eq N j hs (a * b) (repOf N j a * repOf N j b)
      (fun Q => by rw [map_mul, repOf_spec, repOf_spec, Pi.mul_apply, map_mul]), map_mul]
    rfl
  map_zero' := by
    show rhoFun N j 0 = 0
    rw [rhoFun_eq N j hs 0 0 (fun Q => by rw [map_zero, Pi.zero_apply, map_zero]), map_zero]
  map_add' a b := by
    show rhoFun N j (a + b) = rhoFun N j a + rhoFun N j b
    rw [rhoFun_eq N j hs (a + b) (repOf N j a + repOf N j b)
      (fun Q => by rw [map_add, repOf_spec, repOf_spec, Pi.add_apply, map_add]), map_add]
    rfl
  commutes' x := by
    show rhoFun N j _ = _
    rw [rhoFun_eq N j hs _ (C (algebraMap F E x)) (fun Q => by rw [Pi.algebraMap_apply, hj, AdjoinRoot.mk_C]),
      aeval_C, IsScalarTower.algebraMap_apply F E (Matrix (Fin n) (Fin n) E)]

variable (hs : N.charpoly.Separable)
  (hj : ∀ Q x, j Q (algebraMap F (K Q) x) = AdjoinRoot.of Q.1 (algebraMap F E x))

theorem rho_apply (a : ∀ Q, K Q) : rho N j hs hj a = aeval N (repOf N j a) := rfl

theorem rho_injective : Function.Injective (rho N j hs hj) := by
  intro a b hab
  rw [rho_apply, rho_apply] at hab
  have h := (aeval_eq_iff N hs _ _).1 hab
  funext Q
  apply (j Q).injective
  rw [← repOf_spec N j a Q, ← repOf_spec N j b Q]
  exact h Q

theorem rho_comm (a : ∀ Q, K Q) : rho N j hs hj a * N = N * rho N j hs hj a := by
  rw [rho_apply]
  have h : aeval N (repOf N j a * X) = aeval N (X * repOf N j a) := by rw [mul_comm]
  rwa [map_mul, map_mul, aeval_X] at h

theorem rho_span (s : E)
    (hspan : ∀ (Q : Fac N.charpoly) (z : AdjoinRoot Q.1), ∃ (a b : K Q), z = j Q a + AdjoinRoot.of Q.1 s * j Q b)
    (x : Matrix (Fin n) (Fin n) E) (hx : x * N = N * x) :
    ∃ a b, x = rho N j hs hj a + s • (rho N j hs hj b : Matrix (Fin n) (Fin n) E) := by
  obtain ⟨f, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N x hs hx.symm
  choose a b hab using fun Q => hspan Q (AdjoinRoot.mk Q.1 f)
  refine ⟨a, b, ?_⟩
  rw [rho_apply, rho_apply]
  have h : s • aeval N (repOf N j b) = aeval N (C s * repOf N j b) := by
    rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) E) s, smul_mul_assoc, one_mul]
  rw [h, ← map_add]
  refine (aeval_eq_iff N hs _ _).2 fun Q => ?_
  rw [hab Q, map_add, map_mul, repOf_spec, repOf_spec, AdjoinRoot.mk_C]

theorem rho_adj (c : E →+* E) (hc : ∀ x, c (c x) = x) (δ : GL (Fin n) E) (hN : N = (δ * thetaGL n c δ).val)
    (σ : ∀ Q : Fac N.charpoly, AdjoinRoot Q.1 →+* AdjoinRoot Q.1)
    (hσ : ∀ Q x, σ Q (AdjoinRoot.of Q.1 x) = AdjoinRoot.of Q.1 (c x))
    (hσr : ∀ Q, σ Q (AdjoinRoot.root Q.1) * AdjoinRoot.root Q.1 = 1)
    (hσj : ∀ Q a, σ Q (j Q a) = j Q a) (a : ∀ Q, K Q) :
    rho N j hs hj a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((rho N j hs hj a).map c)ᵀ := by
  rw [rho_apply]
  set f := repOf N j a with hfdef
  have hdet : IsUnit N.det := by
    rw [hN]; exact (Matrix.isUnit_iff_isUnit_det _).1 (δ * thetaGL n c δ).isUnit
  have hdδ : IsUnit δ.val.det := (Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit
  obtain ⟨h, hh⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N N⁻¹ hs
    (by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet])
  have hroot : ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 h * AdjoinRoot.root Q.1 = 1 := by
    intro Q
    have h1 : aeval N (h * X) = aeval N (1 : E[X]) := by
      rw [map_mul, ← hh, aeval_X (R := E) N, map_one, Matrix.nonsing_inv_mul _ hdet]
    have h2 := (aeval_eq_iff N hs _ _).1 h1 Q
    rwa [map_mul, AdjoinRoot.mk_X, map_one] at h2
  have hpoly : aeval N⁻¹ (f.map c) = aeval N f := by
    rw [hh, ← Polynomial.aeval_comp]
    refine (aeval_eq_iff N hs _ _).2 fun Q => ?_
    have hσroot : σ Q (AdjoinRoot.root Q.1) = AdjoinRoot.mk Q.1 h :=
      mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (hroot Q)) ((hσr Q).trans (hroot Q).symm)
    calc AdjoinRoot.mk Q.1 ((f.map c).comp h)
        = aeval (AdjoinRoot.root Q.1) ((f.map c).comp h) := (AdjoinRoot.aeval_eq _).symm
      _ = aeval (AdjoinRoot.mk Q.1 h) (f.map c) := by rw [Polynomial.aeval_comp, AdjoinRoot.aeval_eq]
      _ = σ Q (aeval (AdjoinRoot.root Q.1) f) := by
        rw [aeval_def, aeval_def, eval₂_map, hom_eval₂, hσroot]
        congr 1
        exact RingHom.ext fun x => (hσ Q x).symm
      _ = AdjoinRoot.mk Q.1 f := by
        rw [AdjoinRoot.aeval_eq, hfdef, repOf_spec N j a Q, hσj]
  let _ : StarRing E :=
    { star := c
      star_involutive := hc
      star_mul := fun x y => by
        show c (x * y) = c y * c x
        rw [map_mul, mul_comm]
      star_add := map_add c }
  have hsr : (starRingEnd E) = c := RingHom.ext fun _ => rfl
  have hnrm : GlobalTheory.Tw.nrm δ.val = N := by
    rw [hN, Units.val_mul]
    show δ.val * (GlobalTheory.Tw.Phi n E * ((δ.val)⁻¹)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ) =
      δ.val * (GlobalTheory.Tw.Phi n E * (c.mapMatrix (δ⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi n E)ᵀ)
    rw [Matrix.coe_units_inv]
    rfl
  have hadj := GlobalTheory.BCT.KapMul.adj_aeval δ f
  rw [hnrm, hsr, hpoly] at hadj
  have hadj' : δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹ = aeval N f := hadj
  calc aeval N f * (δ.val * GlobalTheory.Tw.Phi n E)
      = (δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹) * (δ.val * GlobalTheory.Tw.Phi n E) := by
        rw [hadj']
    _ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * ((GlobalTheory.Tw.Phi n E)ᵀ * (δ.val⁻¹ * δ.val) * GlobalTheory.Tw.Phi n E) := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ := by
        rw [Matrix.nonsing_inv_mul _ hdδ, Matrix.mul_one, GlobalTheory.Tw.Model.transpose_mul_Phi, Matrix.mul_one]
    _ = δ.val * GlobalTheory.Tw.Phi n E * ((aeval N f).map c)ᵀ := rfl

end Ev

end CompanionTheory.Rg.BcB.G3.StructP

open CompanionTheory.Rg.BcB.G3.StructP in
theorem CompanionTheory.Rg.BcB.G3.struct_pf (h1 : FactorField) : Struct := by
  intro E _ _ _ s d hs0 hcs hd n δ hP
  obtain ⟨hPm, hPn, hPs, hPr⟩ := hP
  have hdata : ∀ Q : Fac (δ * thE E n δ).val.charpoly, ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : Algebra (maximalRealSubfield E) K) (j : K →+* AdjoinRoot Q.1) (σ : AdjoinRoot Q.1 →+* AdjoinRoot Q.1),
      NumberField.IsTotallyReal K ∧ Module.finrank (maximalRealSubfield E) K = Q.1.natDegree ∧
      (∀ x : (maximalRealSubfield E), j (algebraMap (maximalRealSubfield E) K x) =
        AdjoinRoot.of Q.1 (algebraMap (maximalRealSubfield E) E x)) ∧
      (∀ x : E, σ (AdjoinRoot.of Q.1 x) = AdjoinRoot.of Q.1 (IsCMField.complexConj E x)) ∧
      σ (AdjoinRoot.root Q.1) * AdjoinRoot.root Q.1 = 1 ∧ (∀ a, σ (j a) = j a) ∧
      ∀ z, ∃ a b, z = j a + AdjoinRoot.of Q.1 s * j b :=
    fun Q => h1 E s d hs0 hcs hd Q.1 (fac_monic Q) (fac_roots hPm hPr Q)
  choose K hKf hKn hKa j σ hKr hKdeg hj hσ hσr hσj hspan using hdata
  refine ⟨Fac (δ * thE E n δ).val.charpoly, inferInstance, K, hKf, hKn, hKa, rho _ j hPs hj, card_fac hPs, hKr, ?_, ?_⟩
  · simp_rw [hKdeg]
    rw [← Polynomial.natDegree_prod_of_monic _ _ (fun Q _ => fac_monic Q), prod_fac hPm hPs, hPn]
  · refine ⟨rho_injective _ j hPs hj, ?_, ?_, ?_, ?_⟩
    · show rho _ j hPs hj (algebraMap _ _ d) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E (Matrix (Fin n) (Fin n) E), hd,
        Algebra.algebraMap_eq_smul_one]
    · intro a
      exact rho_adj _ j hPs hj (IsCMField.complexConj E).toRingEquiv.toRingHom
        (fun x => IsCMField.complexConj_apply_apply E x) δ rfl σ hσ hσr hσj a
    · intro a
      exact rho_comm _ j hPs hj a
    · intro x hx
      exact rho_span _ j hPs hj s hspan x hx

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.FactorFieldP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cj (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

theorem emb_cj (φ : E →+* ℂ) : φ.comp (cj E) = (starRingEnd ℂ).comp φ := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E φ x

theorem conj_eq_inv {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

abbrev Good (Q : E[X]) : Prop := ∀ τ : E →+* ℂ, ∀ z ∈ (Q.map τ).roots, ‖z‖ = 1

variable (Q : E[X]) [Fact (Irreducible Q)]

instance finL : Module.Finite E (AdjoinRoot Q) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finite

instance nfL : NumberField (AdjoinRoot Q) := NumberField.of_module_finite E (AdjoinRoot Q)

theorem root_norm (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) : ‖ψ (AdjoinRoot.root Q)‖ = 1 := by
  apply h (ψ.comp (AdjoinRoot.of Q))
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Fact.out : Irreducible Q).ne_zero), Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem csr (h : Good Q) :
    Polynomial.eval₂ ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ Q = 0 := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [Polynomial.hom_eval₂, map_zero, map_inv₀, ← conj_eq_inv (root_norm Q h ψ), ← RingHom.comp_assoc, emb_cj,
    ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero, map_zero]

def sig (h : Good Q) : AdjoinRoot Q →+* AdjoinRoot Q :=
  AdjoinRoot.lift ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ (csr Q h)

theorem sig_of (h : Good Q) (x : E) : sig Q h (AdjoinRoot.of Q x) = AdjoinRoot.of Q (IsCMField.complexConj E x) := by
  unfold sig
  erw [AdjoinRoot.lift_of]
  rfl

theorem sig_root (h : Good Q) : sig Q h (AdjoinRoot.root Q) = (AdjoinRoot.root Q)⁻¹ := by
  unfold sig
  exact AdjoinRoot.lift_root _

theorem emb_sig (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) (x : AdjoinRoot Q) :
    ψ (sig Q h x) = starRingEnd ℂ (ψ x) := by
  have e : ψ.comp (sig Q h) = (starRingEnd ℂ).comp ψ := by
    apply AdjoinRoot.ringHom_ext
    · ext y
      simp only [RingHom.coe_comp, Function.comp_apply, sig_of]
      exact IsCMField.complexEmbedding_complexConj E (ψ.comp (AdjoinRoot.of Q)) y
    · simp only [RingHom.coe_comp, Function.comp_apply, sig_root, map_inv₀]
      rw [conj_eq_inv (root_norm Q h ψ)]
  exact RingHom.congr_fun e x

theorem sig_sig (h : Good Q) (x : AdjoinRoot Q) : sig Q h (sig Q h x) = x := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [emb_sig, emb_sig, Complex.conj_conj]

theorem sig_alg (h : Good Q) (x : maximalRealSubfield E) :
    sig Q h (algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x) =
      algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x := by
  show sig Q h (AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)) =
    AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)
  rw [sig_of]
  congr 1
  exact (IsCMField.complexConj E).commutes x

def Kf (h : Good Q) : IntermediateField (maximalRealSubfield E) (AdjoinRoot Q) :=
  (RingHom.eqLocusField (sig Q h) (RingHom.id _)).toIntermediateField fun x => sig_alg Q h x

theorem mem_Kf (h : Good Q) {x : AdjoinRoot Q} : x ∈ Kf Q h ↔ sig Q h x = x := Iff.rfl

theorem totReal (h : Good Q) : IsTotallyReal (Kf Q h) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  letI : Algebra (Kf Q h) ℂ := w.embedding.toAlgebra
  let ψ : AdjoinRoot Q →ₐ[Kf Q h] ℂ := IsAlgClosed.lift
  ext x
  have hx : w.embedding x = ψ.toRingHom (x : AdjoinRoot Q) := (ψ.commutes x).symm
  rw [ComplexEmbedding.conjugate_coe_eq, hx, ← emb_sig Q h ψ.toRingHom, (mem_Kf Q h).1 x.2]

theorem decomp (h : Good Q) {S : AdjoinRoot Q} (hS : S ≠ 0) (hσS : sig Q h S = -S) (z : AdjoinRoot Q) :
    ∃ a b : Kf Q h, z = (a : AdjoinRoot Q) + S * (b : AdjoinRoot Q) := by
  have h2 : (2 : AdjoinRoot Q) ≠ 0 := two_ne_zero
  refine ⟨⟨(z + sig Q h z) / 2, ?_⟩, ⟨(z - sig Q h z) / (2 * S), ?_⟩, ?_⟩
  · rw [mem_Kf, map_div₀, map_add, sig_sig, map_ofNat]
    ring
  · rw [mem_Kf, map_div₀, map_sub, map_mul, sig_sig, map_ofNat, hσS]
    field_simp
    ring
  · show z = (z + sig Q h z) / 2 + S * ((z - sig Q h z) / (2 * S))
    field_simp
    ring

theorem finrank_KL (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (Kf Q h) (AdjoinRoot Q) = 2 := by
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q h (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  have hle : Module.finrank (Kf Q h) (AdjoinRoot Q) ≤ 2 := by
    have hspan : Submodule.span (Kf Q h) (Set.range ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]) = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨a, b, hz⟩ := decomp Q h hS hσS z
      have e : z = a • (1 : AdjoinRoot Q) + b • AdjoinRoot.of Q s := by
        rw [hz, Algebra.smul_def, Algebra.smul_def, mul_one]
        exact congrArg (fun t => (a : AdjoinRoot Q) + t) (mul_comm _ _)
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
    have := finrank_range_le_card (R := Kf Q h) ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
    exact this
  have hne1 : Module.finrank (Kf Q h) (AdjoinRoot Q) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot Q) one_ne_zero).1 h1 (AdjoinRoot.of Q s)
    rw [Algebra.smul_def, mul_one] at hc
    have hm : AdjoinRoot.of Q s ∈ Kf Q h := hc ▸ c.2
    rw [mem_Kf, hσS] at hm
    have h2 : (2 : AdjoinRoot Q) * AdjoinRoot.of Q s = 0 := by linear_combination (-1 : AdjoinRoot Q) * hm
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hS h3
  have hpos : 0 < Module.finrank (Kf Q h) (AdjoinRoot Q) := Module.finrank_pos
  omega

theorem finrank_Kf (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (maximalRealSubfield E) (Kf Q h) = Q.natDegree := by
  have h1 := Module.finrank_mul_finrank (maximalRealSubfield E) E (AdjoinRoot Q)
  haveI : IsScalarTower (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := Module.finrank_mul_finrank (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h1
  rw [finrank_KL Q h hs hsc] at h2
  omega

end CompanionTheory.Rg.BcB.G3.FactorFieldP

open CompanionTheory.Rg.BcB.G3.FactorFieldP in
theorem CompanionTheory.Rg.BcB.G3.factorField_pf : FactorField := by
  intro E _ _ _ s d hs hsc hd Q _ hmon hQ
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q hQ (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  refine ⟨Kf Q hQ, inferInstance, inferInstance, inferInstance, (Kf Q hQ).val.toRingHom, sig Q hQ,
    totReal Q hQ, finrank_Kf Q hQ hs hsc, fun x => rfl, fun x => sig_of Q hQ x, ?_, fun a => a.2, ?_⟩
  · rw [sig_root, inv_mul_cancel₀]
    intro h0
    let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have := root_norm Q hQ ψ
    rw [h0, map_zero, norm_zero] at this
    exact zero_ne_one this
  · intro z
    obtain ⟨a, b, hz⟩ := decomp Q hQ hS hσS z
    exact ⟨a, b, hz⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.QuadFieldP

open QuadraticAlgebra

theorem not_sq_of_real (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E)
    (d : maximalRealSubfield E) (hs0 : s ≠ 0) (hs : IsCMField.complexConj E s = -s)
    (hd : algebraMap (maximalRealSubfield E) E d = s ^ 2) (K : Type) [Field K]
    [Algebra (maximalRealSubfield E) K] (τ : K →+* ℂ) (t : ℂ) (ht : starRingEnd ℂ t = t) :
    t ^ 2 ≠ τ (algebraMap (maximalRealSubfield E) K d) := by
  intro h
  let _ := (τ.comp (algebraMap (maximalRealSubfield E) K)).toAlgebra
  let φ : E →ₐ[maximalRealSubfield E] ℂ := IsAlgClosed.lift
  have h1 : (φ s) ^ 2 = τ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← map_pow, ← hd, φ.commutes]; rfl
  have hu : starRingEnd ℂ (φ s) = - φ s := by
    have h' := IsCMField.complexEmbedding_complexConj E φ.toRingHom s
    simpa [hs] using h'.symm
  have hu0 : φ s ≠ 0 := by
    intro h0; exact hs0 (φ.toRingHom.injective (by simpa using h0))
  rw [← h1] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h2 | h2
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by rw [← h2]; exact ht
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by
      have := congrArg Neg.neg ht
      rw [h2, map_neg, neg_neg, neg_neg] at this
      exact this
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3

end CompanionTheory.Rg.BcB.G3.QuadFieldP

namespace CompanionTheory.Rg.BcB.G3

open QuadFieldP QuadraticAlgebra in
theorem quadField_pf : QuadField := by
  intro E _ _ _ s d hs0 hs hd K _ _ _ hKr
  refine ⟨?_, ?_⟩
  · rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← IsCMField.card_infinitePlace_eq_card_infinitePlace E,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) K, mul_comm]
  generalize hδ : algebraMap (maximalRealSubfield E) K d = δ
  have hkey : ∀ (τ : K →+* ℂ) (t : ℂ), starRingEnd ℂ t = t → t ^ 2 ≠ τ δ := by
    intro τ t ht
    rw [← hδ]
    exact not_sq_of_real E s d hs0 hs hd K τ t ht
  have hns : ∀ r : K, r ^ 2 ≠ δ + 0 * r := by
    intro r hr
    let τ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have hre := ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)
    refine hkey τ (τ r) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [← map_pow, hr, zero_mul, add_zero]
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := ⟨hns⟩
  have hq := GlobalTheory.QuadSymbol.Model.isQuadratic δ
  have hnf := GlobalTheory.QuadSymbol.Model.numberField δ
  have : FiniteDimensional K (QuadraticAlgebra K δ 0) :=
    Module.Finite.of_basis (QuadraticAlgebra.basis δ 0)
  refine ⟨QuadraticAlgebra K δ 0, inferInstance, hnf, inferInstance, hq, ?_, ?_, ?_⟩
  · refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro hre
    let e := w.embedding
    refine hkey (e.comp (algebraMap K _)) (e (ω : QuadraticAlgebra K δ 0)) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [RingHom.comp_apply, ← map_pow, sq, omega_mul_omega_eq_algebraMap]; simp
  · intro x
    rw [GlobalTheory.QuadSymbol.mem_globalNorms_iff]
    have key := GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt (A := K) δ (x := x)
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff] at key
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at key
    rw [← key]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(Algebra.TensorProduct.lid K _).symm z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
    · rintro ⟨z, hz⟩
      refine ⟨Algebra.TensorProduct.lid K _ z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
  · intro u x
    exact GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt δ

end CompanionTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.LocDictP

theorem frame_transport {k : Type} [Field k] {n : ℕ} {c : k →+* k} {δ : GL (Fin n) k} {s : k} {B B' : Type}
    [CommRing B] [CommRing B'] {d : B} {ρ : B →+* Matrix (Fin n) (Fin n) k} (e : B ≃+* B')
    (h : IsFrame c δ s d ρ) : IsFrame c δ s (e d) (ρ.comp e.symm.toRingHom) where
  inj := h.inj.comp e.symm.injective
  sq := by simpa using h.sq
  adj a := h.adj (e.symm a)
  comm a := h.comm (e.symm a)
  span x hx := by
    obtain ⟨a, b, hab⟩ := h.span x hx
    exact ⟨e a, e b, by simpa using hab⟩

theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs0 : s ≠ 0)
    (hsc : IsCMField.complexConj E s = -s) (z : E) :
    ∃ a b : (maximalRealSubfield E),
      z = algebraMap (maximalRealSubfield E) E a + s * algebraMap (maximalRealSubfield E) E b := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (z + IsCMField.complexConj E z) / 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat,
      add_comm]
  have hb : (z - IsCMField.complexConj E z) / (2 * s) ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat,
      hsc]
    field_simp
    ring
  refine ⟨⟨_, ha⟩, ⟨_, hb⟩, ?_⟩
  change z = (z + IsCMField.complexConj E z) / 2 + s * ((z - IsCMField.complexConj E z) / (2 * s))
  field_simp
  ring

end CompanionTheory.Rg.BcB.G3.LocDictP

open CompanionTheory.Rg.BcB.G3.LocDictP in
theorem CompanionTheory.Rg.BcB.G3.locDict_pf (h1 : ClsNorm) (h2 : ClsOnto) (h3 : ClsEq) (h4 : BaseFrame) (h5 : InertBase)
    (h6 : SplitSq) (h7 : TensorCompl) : LocDict := by
  intro E _ _ _ hU s d hs0 hsc hd n δ hsep ι _ K _ _ _ ρ hfr w y hy
  have hdne : d ≠ 0 := by
    rintro rfl
    apply hs0
    have : s ^ 2 = 0 := by rw [← hd, map_zero]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  by_cases hw : IsSplitAt w
  ·
    have hthL : thL n w = MonoidHom.id _ := by simp only [thL, if_pos hw]
    have hy' : y.val.charpoly = atPl w (δ * thE E n δ).val.charpoly := by
      have := hy; simp only [nrmL, if_pos hw] at this; exact this
    refine ⟨fun _ _ => 1, fun t => ⟨fun _ => ?_, fun _ => ?_⟩⟩
    · intro i u
      obtain ⟨r, hr⟩ := h6 E s d hs0 hsc hd w hw
      obtain ⟨e, he⟩ := h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
      have hq : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u =
          algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := by
        rw [← he, ← Pi.mul_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, ← hr, mul_one,
          Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
      have hti : ((t : ∀ i, K i) i) ≠ 0 := ((t.isUnit.map (Pi.evalRingHom K i)).ne_zero)
      have hT : algebraMap (K i) (u.1.adicCompletion (K i)) ((t : ∀ i, K i) i) ≠ 0 := (_root_.map_ne_zero _).2 hti
      have hD : algebraMap (K i) (u.1.adicCompletion (K i)) (algebraMap (maximalRealSubfield E) (K i) d) ≠ 0 :=
        (_root_.map_ne_zero _).2 ((_root_.map_ne_zero _).2 hdne)
      have hq0 : e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hq; exact hD hq.symm
      refine ⟨(1 + (algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹) / 2,
        ((algebraMap (K i) _ ((t : ∀ i, K i) i))⁻¹ - 1) / (2 * e (r ⊗ₜ[maximalRealSubfield E] (1 : K i)) u), ?_⟩
      have : CharZero (u.1.adicCompletion (K i)) :=
        charZero_of_injective_algebraMap (algebraMap (K i) (u.1.adicCompletion (K i))).injective
      simp only [Units.val_one]
      rw [← hq]
      field_simp
      ring
    · have hinv : ∀ x : E, (IsCMField.complexConj E).toRingEquiv.toRingHom
          ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = x := fun x => IsCMField.complexConj_apply_apply E x
      have hN := h1 E n _ hinv δ s hs0 hsc (∀ i, K i) _ ρ.toRingHom hfr t
      have hloc : locEl n w (pt δ ρ.toRingHom t) =
          GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (δ * thE E n δ) := by
        simp only [locEl, if_pos hw, thE, hN]
      have hc1 : y.val.charpoly = (locEl n w (pt δ ρ.toRingHom t)).val.charpoly := by
        rw [hloc, hy']
        change _ = (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly
        rw [Matrix.charpoly_map]
      obtain ⟨h, hh⟩ := GlobalTheory.SepConj.conj_of_charpoly_eq_of_separable _ n y _ hc1 (hy' ▸ hsep.map)
      exact ⟨h, by rw [hthL, MonoidHom.id_apply]; exact hh⟩
  ·
    have hI := GlobalTheory.ConjAtPlace.main E hU w
    have hcc : ∀ x, cj w (cj w x) = x := hI.2.1
    have hcE := (hI.2.2.2.1 hw).1
    have : CharZero (w.adicCompletion E) :=
      charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
    obtain ⟨j, hj1, hj2, hj3⟩ := h5 E hU s d hs0 hsc hd w hw
    obtain ⟨ρ', hρ'1, hρ'⟩ := h4 (maximalRealSubfield E) E
      ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) (w.adicCompletion E)
      (algebraMap E _) j (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) s d hj1 (fun x => hcE x) hj2 hs0 hsc
      (decomp E s hs0 hsc) hj3 n δ hsep (∀ i, K i) ρ hfr
    have hTC := fun i => h7 (maximalRealSubfield E) (K i) (w.under (𝓞 (maximalRealSubfield E)))
    choose e he using hTC
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E]
        (∀ i, K i)) ≃+* (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)),
        ∀ a : (∀ i, K i), Φ (1 ⊗ₜ a) = fun i u => algebraMap (K i) _ (a i) :=
      ⟨(Algebra.TensorProduct.piRight (maximalRealSubfield E) (maximalRealSubfield E) _ K).toRingEquiv.trans
        (RingEquiv.piCongrRight e), fun a => by
          funext i u
          simp [Algebra.TensorProduct.piRight_tmul, he]⟩
    have hfr'' := frame_transport Φ hρ'
    have hmapθ := GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E))
      (IsCMField.complexConj E).toRingEquiv.toRingHom (cj w) (fun x => (hcE x).symm) δ
    have hNδ : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly =
        atPl w (δ * thE E n δ).val.charpoly := by
      rw [← hmapθ, ← map_mul]
      change (((δ * thE E n δ).val).map (algebraMap E (w.adicCompletion E))).charpoly = _
      rw [Matrix.charpoly_map]
    have hsep' : (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly.Separable := by
      rw [hNδ]; exact hsep.map
    have hy' : (y * thetaGL n (cj w) y).val.charpoly = (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ *
        thetaGL n (cj w) (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)).val.charpoly := by
      rw [hNδ]
      have := hy; simp only [nrmL, if_neg hw] at this; exact this
    have hs0' : algebraMap E (w.adicCompletion E) s ≠ 0 := (_root_.map_ne_zero _).2 hs0
    have hsc' : cj w (algebraMap E (w.adicCompletion E) s) = -algebraMap E (w.adicCompletion E) s := by
      rw [hcE, hsc, map_neg]
    obtain ⟨t0, g0, hg0⟩ := h2 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' hsep' y hy'
    refine ⟨fun i u => Units.map (Pi.evalMonoidHom _ u) (Units.map (Pi.evalMonoidHom _ i) t0), fun t => ?_⟩
    obtain ⟨T, hT⟩ : ∃ T : (∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i))ˣ,
        (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) = Φ (1 ⊗ₜ (t : ∀ i, K i)) :=
      ⟨Units.map (Φ.toMonoidHom.comp
        (Algebra.TensorProduct.includeRight : (∀ i, K i) →ₐ[maximalRealSubfield E] _).toRingHom.toMonoidHom) t, rfl⟩
    have hpt : locEl n w (pt δ ρ.toRingHom t) = pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
        (ρ'.comp Φ.symm.toRingHom) T := by
      apply Units.ext
      simp only [locEl, if_neg hw, pt]
      change ((ρ t * δ.val).map (algebraMap E (w.adicCompletion E))) =
        ρ' (Φ.symm (T : _)) * (δ.val.map (algebraMap E (w.adicCompletion E)))
      rw [hT, RingEquiv.symm_apply_apply, hρ'1, Matrix.map_mul]
    have hthL : thL n w = thetaGL n (cj w) := by simp only [thL, if_neg hw]
    rw [hpt, hthL]
    have step1 : (∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ) (ρ'.comp Φ.symm.toRingHom) T =
        g⁻¹ * y * thetaGL n (cj w) g) ↔ ∃ g, pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
          (ρ'.comp Φ.symm.toRingHom) T = g⁻¹ * pt (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ)
            (ρ'.comp Φ.symm.toRingHom) t0 * thetaGL n (cj w) g := by
      rw [hg0]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g0 * g, by rw [hg, map_mul]; group⟩
      · rintro ⟨g, hg⟩
        exact ⟨g0⁻¹ * g, by rw [hg, map_mul, map_inv]; group⟩
    rw [step1, h3 (w.adicCompletion E) n (cj w) hcc _ _ hs0' hsc' _ _ _ hfr'' t0 T]
    have hTv : ∀ i u, (T : ∀ i, ∀ u : {u : HeightOneSpectrum (𝓞 (K i)) // u.under (𝓞 (maximalRealSubfield E)) =
          w.under (𝓞 (maximalRealSubfield E))}, u.1.adicCompletion (K i)) i u =
        algebraMap (K i) _ ((t : ∀ i, K i) i) := fun i u => by rw [hT, hΦ]
    have hdv : ∀ i u, Φ (1 ⊗ₜ algebraMap (maximalRealSubfield E) (∀ i, K i) d) i u =
        algebraMap (K i) _ (algebraMap (maximalRealSubfield E) (K i) d) := fun i u => by rw [hΦ]; rfl
    constructor
    · rintro ⟨U, V, hUV⟩ i u
      refine ⟨U i u, V i u, ?_⟩
      have := congrFun (congrFun hUV i) u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv] at this
      simpa using this
    · intro h
      choose a b hab using h
      refine ⟨fun i u => a i u, fun i u => b i u, ?_⟩
      funext i u
      simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, hTv, hdv]
      simpa using hab i u
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.BaseFrameP

theorem phi_map {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (n : ℕ) :
    (GlobalTheory.Tw.Phi n R).map p = GlobalTheory.Tw.Phi n S := by
  ext i k
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

end CompanionTheory.Rg.BcB.G3.BaseFrameP

open CompanionTheory.Rg.BcB.G3.BaseFrameP in
theorem CompanionTheory.Rg.BcB.G3.baseFrame_pf : BaseFrame := by
  intro F E F' E' _ _ _ _ _ _ _ p j c c' s d hj hc hcj hs0 hcs hspE hspE' n δ hsep B _ _ ρ hfr
  have hps0 : p s ≠ 0 := (map_ne_zero p).2 hs0
  have hcps : c' (p s) = - p s := by rw [hc, hcs, map_neg]
  have indep' : ∀ u v : F', j u + p s * j v = 0 → u = 0 ∧ v = 0 := by
    intro u v h
    have h2 := congrArg c' h
    simp only [map_add, map_mul, hcj, hcps, map_zero] at h2
    have hu : j u = 0 := by
      have h3 : (2 : E') * j u = 0 := by linear_combination h + h2
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    have hv : j v = 0 := by
      rw [hu, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hps0
    exact ⟨(map_eq_zero j).1 hu, (map_eq_zero j).1 hv⟩
  have indepE : ∀ a b : F, algebraMap F E a + s * algebraMap F E b = 0 → a = 0 ∧ b = 0 := by
    intro a b h
    have h1 := congrArg p h
    simp only [map_add, map_mul, ← hj, map_zero] at h1
    obtain ⟨h2, h3⟩ := indep' _ _ h1
    exact ⟨(map_eq_zero (algebraMap F F')).1 h2, (map_eq_zero (algebraMap F F')).1 h3⟩
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    apply indepE a b
    simp only [Algebra.smul_def] at h
    linear_combination h
  have hsp : ⊤ ≤ Submodule.span F (Set.range ![(1 : E), s]) := by
    intro z _
    obtain ⟨a, b, rfl⟩ := hspE z
    have h1 : (1 : E) ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨0, rfl⟩
    have h2 : s ∈ Submodule.span F (Set.range ![(1 : E), s]) := Submodule.subset_span ⟨1, rfl⟩
    have h3 := Submodule.add_mem _ (Submodule.smul_mem _ a h1) (Submodule.smul_mem _ b h2)
    convert h3 using 1
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  obtain ⟨bE, hb0, hb1⟩ : ∃ bE : Module.Basis (Fin 2) F E, bE 0 = 1 ∧ bE 1 = s :=
    ⟨Module.Basis.mk hli hsp, by simp, by simp⟩
  have hdec : ∀ e : E, e = algebraMap F E (bE.repr e 0) + s * algebraMap F E (bE.repr e 1) := by
    intro e
    conv_lhs => rw [← bE.sum_repr e]
    rw [Fin.sum_univ_two, hb0, hb1, Algebra.smul_def, Algebra.smul_def]
    ring
  have hsq : ρ (algebraMap F B d) = s ^ 2 • (1 : Matrix (Fin n) (Fin n) E) := hfr.sq
  have hadj : ∀ a, ρ a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((ρ a).map c)ᵀ := hfr.adj
  have hcm : ∀ a, ρ a * (δ * thetaGL n c δ).val = (δ * thetaGL n c δ).val * ρ a := hfr.comm

  obtain ⟨ρ', hρt⟩ : ∃ ρ' : F' ⊗[F] B →+* Matrix (Fin n) (Fin n) E',
      ∀ x b, ρ' (x ⊗ₜ b) = j x • (ρ b).map p := by
    let _ : Algebra F E' := (p.comp (algebraMap F E)).toAlgebra
    let pA : E →ₐ[F] E' := { p with commutes' := fun _ => rfl }
    let fA : F' →ₐ[F] Matrix (Fin n) (Fin n) E' :=
      { (Matrix.scalar (Fin n) : E' →+* Matrix (Fin n) (Fin n) E').comp j with
        commutes' := fun x => by
          show Matrix.scalar (Fin n) (j (algebraMap F F' x)) = _
          rw [hj, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
          rfl }
    let gA : B →ₐ[F] Matrix (Fin n) (Fin n) E' := pA.mapMatrix.comp ρ
    have hcomm : ∀ x y, Commute (fA x) (gA y) := fun x y => by
      show Commute (Matrix.scalar (Fin n) (j x)) _
      exact Matrix.scalar_commute _ (fun _ => Commute.all _ _) _
    refine ⟨(Algebra.TensorProduct.lift fA gA hcomm).toRingHom, fun x b => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul]
    show Matrix.scalar (Fin n) (j x) * (ρ b).map p = _
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hρ1 : ∀ a, ρ' (1 ⊗ₜ a) = (ρ a).map p := by
    intro a; rw [hρt, map_one, one_smul]
  have hρu : ∀ u : F', ρ' (u ⊗ₜ (1 : B)) = j u • (1 : Matrix (Fin n) (Fin n) E') := by
    intro u; rw [hρt, map_one ρ, Matrix.map_one _ (map_zero p) (map_one p)]
  have hD : ρ' ((1 : F') ⊗ₜ algebraMap F B d) = (p s) ^ 2 • (1 : Matrix (Fin n) (Fin n) E') := by
    rw [hρ1, hsq]
    ext i k
    by_cases h : i = k <;> simp [h, Matrix.one_apply]
  have hN' : (GeneralLinearGroup.map p δ * thetaGL n c' (GeneralLinearGroup.map p δ)).val =
      (δ * thetaGL n c δ).val.map p := by
    rw [← GlobalTheory.ThetaPull.map_thetaGL p c c' (fun x => (hc x).symm) δ, ← map_mul]
    rfl
  refine ⟨ρ', hρ1, ⟨?_, hD, ?_, ?_, ?_⟩⟩
  ·
    obtain ⟨φ, hφdef⟩ : ∃ φ : B →ₗ[F] (Fin n × Fin n × Fin 2 → F),
        ∀ b i, φ b i = bE.repr (ρ b i.1 i.2.1) i.2.2 :=
      ⟨{ toFun := fun b i => bE.repr (ρ b i.1 i.2.1) i.2.2
         map_add' := fun a b => by funext i; simp [map_add]
         map_smul' := fun r b => by funext i; simp [map_smul] }, fun _ _ => rfl⟩
    have hφ : Function.Injective φ := by
      refine (injective_iff_map_eq_zero φ).2 fun b hb => ?_
      have h1 : ρ b = 0 := by
        ext i k
        have h2 : bE.repr (ρ b i k) = 0 := by
          ext t
          have := congrFun hb (i, k, t)
          rw [hφdef] at this
          simpa using this
        simpa using h2
      exact (injective_iff_map_eq_zero ρ.toRingHom).1 hfr.inj b h1
    have hL : Function.Injective (φ.lTensor F') := Module.Flat.lTensor_preserves_injective_linearMap φ hφ
    have hkey : ∀ X : F' ⊗[F] B, ∀ i k, ρ' X i k =
        j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 0)) +
        p s * j (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) (i, k, 1)) := by
      intro X i k
      induction X using TensorProduct.induction_on with
      | zero => simp
      | tmul x b =>
        rw [hρt]
        simp only [LinearMap.lTensor_tmul, TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul, hφdef, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
          Algebra.smul_def, map_mul]
        conv_lhs => rw [hdec (ρ b i k)]
        simp only [map_add, map_mul, ← hj]
        ring
      | add X Y hX hY =>
        simp only [map_add, Matrix.add_apply, hX, hY, Pi.add_apply]
        ring
    refine (injective_iff_map_eq_zero ρ').2 fun X hX => ?_
    have hW : TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2) (φ.lTensor F' X) = 0 := by
      funext ⟨i, k, t⟩
      have h := hkey X i k
      rw [hX, Matrix.zero_apply] at h
      obtain ⟨h0, h1⟩ := indep' _ _ h.symm
      have ht : t = 0 ∨ t = 1 := by fin_cases t <;> simp
      rcases ht with rfl | rfl
      · exact h0
      · exact h1
    have h0 : φ.lTensor F' X = 0 :=
      (TensorProduct.piScalarRight F F F' (Fin n × Fin n × Fin 2)).injective (hW.trans (map_zero _).symm)
    exact hL (by rw [h0, map_zero])
  ·
    intro X
    rw [show (GeneralLinearGroup.map p δ).val = δ.val.map p from rfl, ← phi_map p n, ← Matrix.map_mul]
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt]
      have e1 : ((j x • (ρ b).map p).map c') = j x • (((ρ b).map c).map p) := by
        ext i k; simp [hcj, hc]
      rw [e1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      rw [← Matrix.map_mul, hadj, ← Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_map, Matrix.transpose_map]
    | add X Y hX hY =>
      rw [map_add, add_mul, hX, hY, Matrix.map_add _ (map_add c'), Matrix.transpose_add, mul_add]
  ·
    intro X
    rw [hN']
    induction X using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      rw [hρt, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.map_mul, hcm]
    | add X Y hX hY =>
      rw [map_add, add_mul, mul_add, hX, hY]
  ·
    intro x hx
    rw [hN'] at hx
    have hsepN' : ((δ * thetaGL n c δ).val.map p).charpoly.Separable := by
      rw [Matrix.charpoly_map]; exact hsep.map
    obtain ⟨q, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm _ x hsepN' hx.symm
    have hTadd : ∀ y z : Matrix (Fin n) (Fin n) E', (∃ a b, y = ρ' a + p s • ρ' b) →
        (∃ a b, z = ρ' a + p s • ρ' b) → ∃ a b, y + z = ρ' a + p s • ρ' b := by
      rintro y z ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
      exact ⟨a + a', b + b', by rw [map_add, map_add, smul_add]; abel⟩
    have hT0 : ∃ a b, (0 : Matrix (Fin n) (Fin n) E') = ρ' a + p s • ρ' b := ⟨0, 0, by simp⟩
    have hTsmul : ∀ (e : E') (y : Matrix (Fin n) (Fin n) E'), (∃ a b, y = ρ' a + p s • ρ' b) →
        ∃ a b, e • y = ρ' a + p s • ρ' b := by
      rintro e y ⟨a, b, rfl⟩
      obtain ⟨u, v, rfl⟩ := hspE' e
      refine ⟨(u ⊗ₜ (1 : B)) * a + ((1 : F') ⊗ₜ algebraMap F B d) * ((v ⊗ₜ (1 : B)) * b),
        (u ⊗ₜ (1 : B)) * b + (v ⊗ₜ (1 : B)) * a, ?_⟩
      simp only [map_add, map_mul, hρu, hD, Matrix.smul_mul, one_mul]
      module
    have hTpow : ∀ k : ℕ, ∃ a b, ((δ * thetaGL n c δ).val.map p) ^ k = ρ' a + p s • ρ' b := by
      intro k
      obtain ⟨a, b, hab⟩ := hfr.span ((δ * thetaGL n c δ).val ^ k)
        (Commute.self_pow (δ * thetaGL n c δ).val k).eq.symm
      refine ⟨1 ⊗ₜ a, 1 ⊗ₜ b, ?_⟩
      have hpw : ((δ * thetaGL n c δ).val.map p) ^ k = ((δ * thetaGL n c δ).val ^ k).map p :=
        (map_pow p.mapMatrix _ k).symm
      rw [hpw, hρ1, hρ1, hab]
      ext i k
      simp
    rw [aeval_eq_sum_range]
    exact Finset.sum_induction _ (fun y => ∃ a b, y = ρ' a + p s • ρ' b) hTadd hT0
      (fun i _ => hTsmul _ _ (hTpow i))
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.InertBaseP

theorem exists_real (E : Type) [Field E] [NumberField E] [IsCMField E] (y : E)
    (hy : IsCMField.complexConj E y = y) :
    ∃ p : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E p = y := by
  have h := (IsCMField.complexConj_eq_self_iff (K := E) (x := y)).1 hy
  exact ⟨⟨y, h⟩, rfl⟩

theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs : s ≠ 0)
    (hcs : IsCMField.complexConj E s = -s) (x : E) :
    ∃ p q : maximalRealSubfield E, x = algebraMap _ E p + s * algebraMap _ E q := by
  obtain ⟨p, hp⟩ := exists_real E ((x + IsCMField.complexConj E x) / 2) (by
    rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat]; ring)
  obtain ⟨q, hq⟩ := exists_real E ((x - IsCMField.complexConj E x) / (2 * s)) (by
    rw [map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcs]
    field_simp; ring)
  refine ⟨p, q, ?_⟩
  rw [hp, hq]; field_simp; ring

end CompanionTheory.Rg.BcB.G3.InertBaseP

namespace CompanionTheory.Rg.BcB.G3

theorem inertBase_pf (h1 : TensorCompl) : InertBase := by
  intro E _ _ _ hU s d hs hcs hd w hw
  obtain ⟨hcont, -, -, hin, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨hconj, -⟩ := hin hw
  have h : w.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := rfl
  have hc2 := GlobalTheory.LFun.SplitChart.continuous_complMap (E := E) h
  refine ⟨GlobalTheory.LFun.complMap h, fun x => GlobalTheory.LFun.complMap_algebraMap h x, fun x => ?_, fun z => ?_⟩
  · have heq := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield E)
        (w.under (𝓞 (maximalRealSubfield E)))).equalizer (hcont.comp hc2) hc2 (funext fun a => by
          simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hconj, AlgEquiv.commutes])
    exact congrFun heq x
  · obtain ⟨t, rfl⟩ := GlobalTheory.LFun.ConjPlace.toCompl_surjective h z
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a x =>
      obtain ⟨p, q, hx⟩ := InertBaseP.decomp E s hs hcs x
      refine ⟨a * algebraMap _ _ p, a * algebraMap _ _ q, ?_⟩
      simp only [GlobalTheory.LFun.toCompl_tmul, hx, map_mul, map_add, GlobalTheory.LFun.complMap_algebraMap]
      ring
    | add t1 t2 e1 e2 =>
      obtain ⟨a1, b1, f1⟩ := e1
      obtain ⟨a2, b2, f2⟩ := e2
      exact ⟨a1 + a2, b1 + b2, by rw [map_add, f1, f2, map_add, map_add]; ring⟩

end CompanionTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3

theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end CompanionTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.TensorComplP

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

theorem finite_over : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 F) = v}.Finite := by
  have := v.isMaximal
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := HeightOneSpectrum.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def phi : v.adicCompletion F ⊗[F] K →+*
    (∀ u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}, u.1.adicCompletion K) :=
  RingHom.pi fun u => GlobalTheory.LFun.toCompl u.2

theorem phi_apply (y : v.adicCompletion F ⊗[F] K) (u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}) :
    phi v y u = GlobalTheory.LFun.toCompl u.2 y := rfl

def extZ : v.adicCompletion F ⊗[F] K →ₗ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] K :=
  LinearMap.rTensor K (GlobalTheory.AdelicU.singleFin v)

theorem map_extZ_self (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) (extZ v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_extZ_ne {v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v) (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F K) (extZ v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

theorem phi_injective : Function.Injective (phi (K := K) v) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h0 : GlobalTheory.LFun.finAdEquiv F K (extZ v y) = 0 := by
    have hc : ∀ w : HeightOneSpectrum (𝓞 K), GlobalTheory.LFun.finAdEquiv F K (extZ v y) w = 0 := by
      intro w
      by_cases hw : w.under (𝓞 F) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply hw, map_extZ_self]
        exact (phi_apply v y ⟨w, hw⟩).symm.trans (congrFun hy ⟨w, hw⟩)
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, map_extZ_ne v hw, map_zero]
    exact Subtype.ext (funext hc)
  have h1 : extZ v y = 0 := (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv F K).injective).1 h0
  rw [← map_extZ_self v y, h1, map_zero]

theorem phi_surjective : Function.Surjective (phi (K := K) v) := by
  intro z
  obtain ⟨y, hy⟩ := (GlobalTheory.LFun.finAdEquiv F K).surjective
    ⟨fun w => if h : w.under (𝓞 F) = v then z ⟨w, h⟩ else 0, by
      filter_upwards [(finite_over (K := K) v).compl_mem_cofinite] with u hu
      rw [dif_neg (by simpa using hu)]
      exact zero_mem _⟩
  refine ⟨Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) y, funext fun u => ?_⟩
  rw [phi_apply, ← GlobalTheory.LFun.finAdEquiv_apply u.2, hy]
  show (if h : u.1.under (𝓞 F) = v then z ⟨u.1, h⟩ else 0) = z u
  rw [dif_pos u.2]

end CompanionTheory.Rg.BcB.G3.TensorComplP

open CompanionTheory.Rg.BcB.G3.TensorComplP in
theorem CompanionTheory.Rg.BcB.G3.tensorCompl_pf : TensorCompl := by
  intro F K _ _ _ _ _ v
  refine ⟨RingEquiv.ofBijective (phi v) ⟨phi_injective v, phi_surjective v⟩, fun a u => ?_⟩
  show GlobalTheory.LFun.toCompl u.2 (1 ⊗ₜ[F] a) = _
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3.LocGoodP

theorem nrmL_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z : GLw n w) (hz : z ∈ GlobalTheory.LFun.KGL w n) : nrmL n w z ∈ GlobalTheory.LFun.KGL w n := by
  obtain ⟨-, -, hKθ, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  unfold nrmL
  split_ifs with hs
  · exact hz
  · have : thetaGL n (cj w) z = thL n w z := by unfold thL; rw [if_neg hs]
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem hz (hKθ _ hz)

theorem commute_nrmL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z t : GLw n w) (ht : t ∈ twCent (thL n w) z) : t * nrmL n w z = nrmL n w z * t := by
  obtain ⟨-, hinv, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have ht' : t * z = z * thL n w t := ht
  by_cases hs : IsSplitAt w
  · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
    rw [hn1]; rw [hθ1] at ht'; simpa using ht'
  · have hn1 : nrmL n w z = z * thL n w z := by
      unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
    rw [hn1]
    calc t * (z * thL n w z) = z * thL n w t * thL n w z := by rw [← mul_assoc, ht']
      _ = z * thL n w (t * z) := by simp only [map_mul, mul_assoc]
      _ = z * thL n w (z * thL n w t) := by rw [ht']
      _ = z * thL n w z * t := by simp only [map_mul, hinv, mul_assoc]

end CompanionTheory.Rg.BcB.G3.LocGoodP

open CompanionTheory.Rg.BcB.G3.LocGoodP in
theorem CompanionTheory.Rg.BcB.G3.locGood_pf : LocGood := by
  intro E _ _ _ hU n P hP
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E P hP.2.2.1,
    GlobalTheory.BCT.UnitStable.eventually_separable (E := E) P hP.2.2.1] with w hgood hsep
  intro z hzK hz
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w z).val.charpoly + v * derivative (nrmL n w z).val.charpoly = 1 := by
    rw [hz]; exact hgood
  have hNK := nrmL_mem hU n w z hzK
  refine ⟨fun g hg => ?_, fun t ht hc => ?_, fun y hyK hy => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.SplitUniq.splitUniq E n w z g hzK hgood₀ hg
      refine ⟨t, ?_, k, hk, rfl⟩
      show t * z = z * thL n w t
      rw [hθ1]; exact ht
    · exact GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs z g hzK hgood₀ hg
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w (nrmL n w z) t hNK hgood₀ (commute_nrmL hU n w z t ht) hc
  · exact GlobalTheory.BCT.UnitStable.twConj_of_mem hU n w (atPl w P) hsep z y hz hy hzK hyK
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT CompanionTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem CompanionTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

namespace CompanionTheory.Rg.BcB.G3

theorem param_lit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → ∃ (ι : Type) (_ : Fintype ι) (K L : ι → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Field (L i)) (_ : ∀ i, NumberField (L i)) (_ : ∀ i, Algebra (K i) (L i)) (_ : ∀ i, Algebra.IsQuadraticExtension (K i) (L i)) (x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i)), Fintype.card ι = nfac P ∧ (∀ i, NumberField.IsTotallyReal (K i)) ∧ (∀ i, NumberField.IsTotallyComplex (L i)) ∧ (∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i)) ∧ ∑ i, Fintype.card (InfinitePlace (K i)) = n * Fintype.card (InfinitePlace E) ∧ Nonempty ({c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} ≃ ∀ i, {q : (K i)ˣ ⧸ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) // ∃ t : (K i)ˣ, q = QuotientGroup.mk t ∧ ∀ u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) t u ∈ GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i))}) :=
  param_pfL skewEx_pf (struct_pf factorField_pf) quadField_pf
    (locDict_pf clsNorm_pf clsOnto_pf clsEq_pf baseFrame_pf (inertBase_pf tensorCompl_pf) (splitSq_pf tensorCompl_pf)
      tensorCompl_pf) clsNorm_pf clsOnto_pf clsEq_pf locGood_pf

end CompanionTheory.Rg.BcB.G3
end
