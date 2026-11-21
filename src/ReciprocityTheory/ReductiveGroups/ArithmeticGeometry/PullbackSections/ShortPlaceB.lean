import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ShortPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

def AdaptAt {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : GenLat E n) {K : Type} [Field K] [NumberField K]
    (la : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ k : ℕ, ((k : 𝓞 K) ∉ la.asIdeal) ∧ Ideal.span {(k : 𝓞 E)} • Λ.La ≤ stdLat E n ∧
    Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ.La

def ShortFreeNSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (Λ : GenLat D.host.E n) (N N' : ℕ) (x0 : Fin n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F)
    (f : T.toTop.R j),
    Λ.Unimod → Λ.TrivAt (badN D) → P ∈ harmL T.Q.c Λ a → Λ.LevOK N (T.dδ j n).l₂.M → Λ.LevOK N' (T.dδ j n).l₂.M →
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N' x0 P f

def ShortRepSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
      (∀ p ∈ ({2, D.host.q, D.host.d, D.host.g 0, D.host.g 1, (T.dδ j w.n).pd} : Finset ℕ),
        ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
      ∃ (u : T.Q.c.F) (g' : T.toTop.R j), u ≠ 0 ∧ vLa la u = 0 ∧ g = u • g' ∧
        ∃ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La)
          (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
          g' ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ j w.n).l₂.M ∧
          Λ.LevOK N (T.dδ j w.n).l₂.M ∧ AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 ∧ P ∈ harmL T.Q.c Λ (wtA w) ∧
          AdaptAt Λ la ∧ ((N : 𝓞 T.Q.c.F) ∉ la.asIdeal) ∧ IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g'

def PdOffRamD (D : D7) : Prop :=
  ∀ (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (n : ℕ),
    Nat.Coprime (T.dδ j n).pd (2 * D.host.q * D.host.d)

def ShortValChartSt : Prop :=
  ∀ (D : D7) (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) → ∀ (w : WeightFamilies.Wt D j)
    (g : T.toTop.R j)
    (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F),
    g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M →
    Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) →
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
      ((N : 𝓞 T.Q.c.F) ∉ la.asIdeal) → AdaptAt Λ la →
      ∃ (T' : CDVR) (iT : Tc.Fr →+* T'.Fr) (e' : ℕ), OverLa la T'.V (iT.comp io) e' ∧
      ∃ (yI' : IntFr (T.Q.Xo j) T.Q.c T' (iT.comp io)),
        (letI := io.toAlgebra
         letI := (iT.comp io).toAlgebra
         ∃ φ : Tc.Fr →ₐ[T.Q.c.F] T'.Fr, φ.toRingHom = iT ∧ FrMap φ yI.1 yI'.1) ∧
      ∃ (io₂ : (T.dδ j w.n).c₂.F →+* T'.Fr), (∀ (a : (T.dδ j w.n).c₂.F) (b : T.Q.c.F), (a : ℂ) = b → io₂ a = iT (io b)) ∧
      ∃ (yI₂ : IntFr (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ T' io₂), yI₂.IsAlg ∧
        (letI := (iT.comp io).toAlgebra
         letI := io₂.toAlgebra
         FrOver (T.dδ j w.n) yI₂.1 yI'.1) ∧
      ∃ (C : IntegralChartA3 (T.dδ j w.n).Xo₂ (T.dδ j w.n).c₂ T' io₂ yI₂) (ι : Type) (_ : Fintype ι) (cf : ι → T'.Fr)
        (P' : MvPolynomial (LtN (T.Q.Dw j) w.n) T'.Fr) (gm : ι → Fin w.n → Germ.PS T'.Fr 1 (chD C.ch)) (k : ℕ),
        P' ∈ FFV (Dw := T.Q.Dw j) T' (wtA w) w.n ∧ (∀ i b, IsIntPS T' (gm i b)) ∧ (∀ i, 0 ≤ nval T'.V e' (cf i)) ∧
        letI := io₂.toAlgebra
        nval T'.V e' (∑ i, cf i * ∑ mo ∈ P'.support, P'.coeff mo *
          ∏ b, C.ch.B.nabVal T'.Fr C.ch.h T.Q.H.w0 k (gm i b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1)) ≤
          nval Tc.V e (evI yI g)

def ChartValueIntegralAnyLevel : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (l' : Level T.Q.H) (Xo' : Moduli (T.Q.Dw j) l') (c' : Coeff l') (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr)
      (io' : c'.F →+* Tc.Fr), (∀ (a : c'.F) (b : T.Q.c.F), (a : ℂ) = b → io' a = io b) →
    ∀ (yI : IntFr Xo' c' Tc io') (e : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    (∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∉ la.asIdeal)) →
    ∀ (C : IntegralChartA3 Xo' c' Tc io' yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io'.toAlgebra
        0 ≤ nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
          ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))

def ChartValueRamifiedAnyLevel : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) [StarRing (𝓞 D.host.E)],
    (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ (l' : Level T.Q.H) (Xo' : Moduli (T.Q.Dw j) l') (c' : Coeff l') (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr)
      (io' : c'.F →+* Tc.Fr), (∀ (a : c'.F) (b : T.Q.c.F), (a : ℂ) = b → io' a = io b) →
    ∀ (yI : IntFr Xo' c' Tc io') (e : ℕ) (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ p ∈ ({2, D.host.q, D.host.d} : Finset ℕ), ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
    ∀ (C : IntegralChartA3 Xo' c' Tc io' yI) (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Tc.Fr), P ∈ FFV (Dw := T.Q.Dw j) Tc a n →
      ∀ f : Fin n → Germ.PS Tc.Fr 1 (chD C.ch), (∀ b, IsIntPS Tc (f b)) →
        letI := io'.toAlgebra
        (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * vdP D p * (DF (T.Q.Dw j) a : ℝ) / 2)) : ℝ) : EReal) ≤
          nval Tc.V e (∑ mo ∈ P.support, P.coeff mo *
            ∏ b, C.ch.B.nabVal Tc.Fr C.ch.h T.Q.H.w0 k (f b) C.ch.uvec (MvPolynomial.monomial (colOf mo b) 1))



section Ultra

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem le_nval_sum (e : ℕ) {ι : Type} (s : Finset ι) (f : ι → K') (r : EReal) (h : ∀ i ∈ s, r ≤ nval V e (f i)) :
    r ≤ nval V e (∑ i ∈ s, f i) := by
  classical
  unfold nval at h ⊢
  split_ifs with hs
  · exact le_top
  · have hne : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty] at hn
      exact hs (by rw [hn, Finset.sum_empty])
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s (fun i => valV V (f i)) hne
    have hle : valV V (∑ i ∈ s, f i) ≤ valV V (f i) := Valuation.map_sum_le _ hmax
    have hfi : f i ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hle
      exact hs ((Valuation.zero_iff _).1 (le_antisymm hle zero_le'))
    have h1 := h i hi
    rw [if_neg hfi] at h1
    refine h1.trans ?_
    have hlog := (WithZero.log_le_log ((Valuation.ne_zero_iff _).2 hs) ((Valuation.ne_zero_iff _).2 hfi)).2 hle
    refine EReal.coe_le_coe_iff.2 ?_
    have hl : ((-(valV V (f i)).log : ℤ) : ℝ) ≤ ((-(valV V (∑ i ∈ s, f i)).log : ℤ) : ℝ) := by
      exact_mod_cast neg_le_neg hlog
    exact div_le_div_of_nonneg_right hl (Nat.cast_nonneg e)


end Ultra





def ShortSeriesRamifiedPlaceTwoAt (D : D7) : Prop :=
  ∀ (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la),
      (((2 : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la ((2 : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
          ((D.R.e : ℝ) + 1 - (2 : ℝ)⁻¹ ^ D.R.e) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g

def ShortPlaceBqdAt (D : D7) : Prop :=
  ∀ (T : Full D) (_hF : LawsFull T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j) (g : T.toTop.R j),
    g ∈ T.toTop.sh j w → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (y : T.toTop.PtA j la) (p : ℕ),
      p ∈ ({D.host.q, D.host.d} : Finset ℕ) → ((p : 𝓞 T.Q.c.F) ∈ la.asIdeal) →
      (((-(((vLa la (p : T.Q.c.F) : ℤ) : ℝ) * (1 / 2) * (DF w : ℝ) / 2)) : ℝ) : EReal) ≤ vAtV y g






end ReciprocityTheory.ChartRestriction.G.PullbackSections
