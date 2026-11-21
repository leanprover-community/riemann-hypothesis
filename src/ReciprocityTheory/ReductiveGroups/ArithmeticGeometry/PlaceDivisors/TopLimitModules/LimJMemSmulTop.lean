import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.TL

variable {O : Type} [CommRing O] {d : ℕ}

def Fmod (p : ℕ) (F : FGLaw O d) (n : ℕ) : Fin d → PS (O ⧸ Ideal.span {(p : O) ^ (n + 1)}) 2 d :=
  fun i => MvPowerSeries.map (Ideal.Quotient.mk _) (F.F i)

theorem Fmod_const (p : ℕ) (F : FGLaw O d) (n : ℕ) (i : Fin d) : constantCoeff (Fmod p F n i) = 0 := by
  simp [Fmod, F.const i]

def redQ (p : ℕ) (n : ℕ) : O ⧸ Ideal.span {(p : O) ^ (n + 1 + 1)} →+* O ⧸ Ideal.span {(p : O) ^ (n + 1)} :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ _)))

def jetMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (κ : Type) (k : ℕ) :
    JetR A κ k →+* JetR B κ k :=
  Ideal.quotientMap _ (MvPolynomial.map g) (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, Ideal.map_span]
    refine Ideal.pow_right_mono (Ideal.span_mono ?_) _
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (MvPolynomial.map_X g i).symm⟩)

def LimSt : Prop :=
  ∀ (O : Type) [CommRing O] (p : ℕ) [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d)
    (U : ∀ n k : ℕ, JetR (O ⧸ Ideal.span {(p : O) ^ (n + 1)}) (Fin 1 × Fin d) k), 0 < d →
    (∀ n k, jetMap (redQ p n) (Fin 1 × Fin d) k (U (n + 1) k) = U n k) →
    (∀ n k, jetTruncR _ (Fin 1 × Fin d) k (U n (k + 1)) = U n k) →
    (∀ n k, jetZeroR _ (Fin 1 × Fin d) k (U n k) = 1) →
    (∀ n k, substJ (n := 2) k (Fmod p F n) (Fmod_const p F n) (U n k) =
      jetPt (n := 2) (0 : Fin 2) k (U n k) * jetPt (n := 2) (1 : Fin 2) k (U n k)) →
    ∃ u : PS O 1 d, IsCh F.F u ∧
      ∀ n k, psJet k (MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)})) u) = U n k

end ReciprocityTheory.ChartRestriction.G.Pdiv.TL
end
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.TL

section Jets

variable {T : Type} [CommRing T]

theorem limJ_mk_eq_iff {σ : Type} (k : ℕ) (P Q : MvPolynomial σ T) :
    (Ideal.Quotient.mk _ P : JetR T σ k) = Ideal.Quotient.mk _ Q ↔
      ∀ x : σ →₀ ℕ, x.degree < k + 1 → P.coeff x = Q.coeff x := by
  rw [Ideal.Quotient.eq]
  have hI : (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ T))) =
      MvPolynomial.idealOfVars σ T := rfl
  rw [hI, MvPolynomial.mem_pow_idealOfVars_iff]
  constructor
  · intro h x hx
    by_contra hne
    have hmem : x ∈ (P - Q).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub]
      exact sub_ne_zero.mpr hne
    have := h x hmem
    omega
  · intro h x hx
    by_contra hlt
    push_neg at hlt
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, h x hlt, sub_self] at hx
    exact hx rfl

theorem limJ_tt_eq_iff {σ : Type} [Finite σ] (k : ℕ) (f g : MvPowerSeries σ T) :
    truncTotalAlgHom σ T (k + 1) f = truncTotalAlgHom σ T (k + 1) g ↔
      ∀ x : σ →₀ ℕ, x.degree < k + 1 → coeff x f = coeff x g := by
  rw [MvPowerSeries.truncTotalAlgHom_apply, MvPowerSeries.truncTotalAlgHom_apply]
  refine (limJ_mk_eq_iff k (truncTotal (k + 1) f) (truncTotal (k + 1) g)).trans ?_
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  rw [MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_truncTotal _ hx]

theorem limJ_lt_box {σ : Type} [Finite σ] (i0 : σ) (k : ℕ) (x : σ →₀ ℕ) (hx : x.degree < k + 1) :
    x < Finsupp.equivFunOnFinite.symm (fun _ : σ => k + 1) := by
  classical
  have hle : ∀ i, x i ≤ x.degree := fun i => by
    by_cases hi : i ∈ x.support
    · exact Finset.single_le_sum (f := fun j => x j) (fun _ _ => Nat.zero_le _) hi
    · have h0 : x i = 0 := by
        by_contra h'
        exact hi (Finsupp.mem_support_iff.mpr h')
      rw [h0]
      exact Nat.zero_le _
  refine lt_of_le_of_ne (fun i => ?_) (fun h => ?_)
  · show x i ≤ k + 1
    have := hle i
    omega
  · have h2 : x i0 = k + 1 := by
      rw [h]
      rfl
    have := hle i0
    omega

theorem limJ_psJet_eq {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (f : PS T n d) :
    psJet k f = truncTotalAlgHom (Fin n × Fin d) T (k + 1) f := by
  rw [MvPowerSeries.truncTotalAlgHom_apply]
  refine (limJ_mk_eq_iff k _ _).mpr fun x hx => ?_
  classical
  rw [MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_trunc,
    if_pos (limJ_lt_box (⟨0, hn⟩, ⟨0, hd⟩) k x hx)]












end Jets

section Limits

variable {O : Type} [CommRing O] (p : ℕ) [IsAdicComplete (Ideal.span {(p : O)}) O]





end Limits


end ReciprocityTheory.ChartRestriction.G.Pdiv.TL
end
end
