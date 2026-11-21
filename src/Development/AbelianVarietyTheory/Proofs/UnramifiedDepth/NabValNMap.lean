import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeNabValBaseChange

section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.InvDerCopiesMap

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by
  ext m
  simp [coeff_map, coeff_pderiv]

theorem map_ev_axis {d n : ℕ} (b : Fin n) (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := n) ![pt R d b, 0] g) =
      ev (n := n) ![pt S d b, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  have h : HasSubst (fun p : Fin 2 × Fin d => (![pt R d b, 0] : Fin 2 → Pt R n d) p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    rintro ⟨j, i⟩
    fin_cases j <;> simp [pt]
  rw [MvPowerSeries.map_subst h]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem map_DofN {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f : PS R n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by
  simp only [DofN, map_sum, map_mul, map_C, map_ev_axis, map_pderiv]

theorem map_DofN_iterate {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (k : ℕ)
    (f : PS R n d) :
    MvPowerSeries.map φ ((DofN F b u)^[k] f) =
      (DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)))^[k] (MvPowerSeries.map φ f) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_DofN, ih]

theorem map_DmonN {d n : ℕ} (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n)
    (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R n d) :
    MvPowerSeries.map φ (DmonN F cp u m f) =
      DmonN (fun i => MvPowerSeries.map φ (F i)) cp (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by
  unfold DmonN
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, List.foldr_cons, map_DofN_iterate, ih]

end GlobalTheory.InvDerCopiesMap

namespace GlobalTheory

theorem dpolyN_map : ∀ (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (d n : ℕ) (F : Fin d → PS S 2 d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S) (f : PS S n d), DpolyN (fun i => MvPowerSeries.map ψ (F i)) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) (MvPowerSeries.map ψ f) = MvPowerSeries.map ψ (DpolyN F cp u P f) := by
  intro S S' _ _ ψ d n F κ _ cp u P f
  unfold DpolyN
  rw [Finset.sum_subset (MvPolynomial.support_map_subset ψ P) (fun m _ hm => by
    rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]), map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.map_C, InvDerCopiesMap.map_DmonN, MvPolynomial.coeff_map]

end GlobalTheory
end
end

section
set_option autoImplicit false

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv GlobalTheory.GaugeBaseChange in

theorem nabValN_map : ∀ (S S' : Type) [CommRing S] [Algebra ℚ S] [CommRing S'] [Algebra ℚ S'] (ψ : S →+* S') (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB S d O) (B' : FB S' d O), (∀ i, B'.G.F i = MvPowerSeries.map ψ (B.G.F i)) → (∀ a i, B'.A.act a i = MvPowerSeries.map ψ (B.A.act a i)) → ∀ (h : PS S 2 d), MvPowerSeries.constantCoeff h = 0 → ∀ (w0 : O) (m n : ℕ) (f : PS S n d) (κ : Type) [Fintype κ] (cp : κ → Fin n) (u : κ → Fin d → S) (P : MvPolynomial κ S), nabValN B' S' (MvPowerSeries.map ψ h) w0 m (MvPowerSeries.map ψ f) cp (fun l j => ψ (u l j)) (MvPolynomial.map ψ P) = ψ (nabValN B S h w0 m f cp u P) := by
  intro S S' _ _ _ _ ψ d O _ _ B B' hF hA h hc w0 m n f κ _ cp u P
  have eF : (fun i => MvPowerSeries.map ψ (B.FK S i)) = B'.FK S' := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.G.F i)) =
      MvPowerSeries.map (algebraMap S' S') (B'.G.F i)
    rw [hF]
    ext e
    simp [coeff_map]
  have eA : mapP ψ (B.actK S w0) = B'.actK S' w0 := by
    funext i
    change MvPowerSeries.map ψ (MvPowerSeries.map (algebraMap S S) (B.A.act w0 i)) =
      MvPowerSeries.map (algebraMap S' S') (B'.A.act w0 i)
    rw [hA]
    ext e
    simp [coeff_map]
  have gC : GP (comp1 (B.actK S w0) (pt S (n := 1) d 0)) := gp_comp1 _ _ (gp_actK B w0) (gp_pt 0)
  have cL : constantCoeff (B.hL S h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map ψ (B.hL S h w0) = B'.hL S' (MvPowerSeries.map ψ h) w0 := by
    unfold FB.hL
    rw [map_ev_two _ _ _ (gp_pt _) gC, baseChange_comp1 _ _ _ (gp_pt _), eA, baseChange_pt]
  have g1 : ∀ (b : Fin n) (j : Fin 1), GP ((![pt S d b] : Fin 1 → Pt S n d) j) := by
    intro b j
    fin_cases j
    exact gp_pt b
  have cb : ∀ b : Fin n, constantCoeff (ev (n := n) ![pt S d b] (B.hL S h w0)) = 0 :=
    fun b => gt_const_ev _ (g1 b) _ cL
  have eb : ∀ b : Fin n, MvPowerSeries.map ψ (ev (n := n) ![pt S d b] (B.hL S h w0)) =
      ev (n := n) ![pt S' d b] (B'.hL S' (MvPowerSeries.map ψ h) w0) := by
    intro b
    rw [map_ev ψ _ (g1 b), eL]
    congr 1
    funext j
    fin_cases j
    exact baseChange_pt ψ b
  unfold nabValN
  rw [← MvPowerSeries.constantCoeff_map, ← GlobalTheory.dpolyN_map, eF, map_mul,
    map_expS _ _ (by
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, Finset.sum_eq_zero fun b _ => cb b, mul_zero]),
    MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, map_mul, map_C, map_natCast ψ, map_sum,
    Finset.sum_congr rfl fun b _ => eb b]

end GlobalTheory
end
