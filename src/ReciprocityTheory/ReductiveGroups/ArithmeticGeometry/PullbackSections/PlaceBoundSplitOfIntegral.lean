import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PlaceIntegralUnramified

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

section Val

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K'] [Algebra V K'] [IsFractionRing V K']

theorem nval_nonneg_of_int (e : ℕ) {x : K'} (hx : x ∈ (algebraMap V K').range) : 0 ≤ nval V e x := by
  unfold nval
  split_ifs with h0
  · exact le_top
  · obtain ⟨y, rfl⟩ := hx
    unfold vV
    have hv : valV V ((algebraMap V K') y) ≤ 1 := by
      unfold valV
      exact HeightOneSpectrum.valuation_le_one _ y
    have hne : valV V ((algebraMap V K') y) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have hl : ((valV V) ((algebraMap V K') y)).log ≤ 0 := by
      first
      | exact (WithZero.log_le_log hne one_ne_zero).mpr hv |>.trans_eq WithZero.log_one
      | exact WithZero.log_nonpos hv
      | exact WithZero.log_le_zero_iff.mpr hv
      | simpa using WithZero.log_mono hne hv
    have h1 : (0:ℝ) ≤ ((-(valV V ((algebraMap V K') y)).log : ℤ) : ℝ) / (e : ℝ) :=
      div_nonneg (by exact_mod_cast (by omega : (0:ℤ) ≤ -(valV V ((algebraMap V K') y)).log)) (Nat.cast_nonneg _)
    exact EReal.coe_nonneg.mpr h1



end Val

def NnIntCSt : Prop :=
  ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (nab : NabV (T.Q.Xo j) T.Q.c),
    (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.Q.Xo j) T.Q.c nab) → ∀ (w : WeightFamilies.Wt D j) (x : Fin w.n → (T.Q.Dw j).La)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n →
    ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c nab x P f →
    ∀ (Tc : CDVR) (io : T.Q.c.F →+* Tc.Fr) (yI : IntFr (T.Q.Xo j) T.Q.c Tc io) (e : ℕ)
      (la : HeightOneSpectrum (𝓞 T.Q.c.F)), OverLa la Tc.V io e → yI.IsAlg →
    ∀ (i : Fin 2) (πE : 𝓞 D.host.E) (τ : D.host.E →+* ℂ),
      InPsi T.Q.H τ → πE * T.Q.H.bar πE = (D.host.g i : 𝓞 D.host.E) →
      T.Q.l.Mb ≤ Ideal.span {T.Q.H.bar πE} → ((D.host.g i : 𝓞 T.Q.c.F) ∈ la.asIdeal) → D.host.g i ≠ D.host.q →
      io (embK T.Q.c τ πE) ^ (∑ t, ∑ k, w.aP t k) *
        (io (embK T.Q.c τ (T.Q.H.bar πE)) ^ (∑ t, ∑ k, w.aM t k) * evI yI f) ∈ (algebraMap Tc.V Tc.Fr).range


end ReciprocityTheory.ChartRestriction.G.PullbackSections
