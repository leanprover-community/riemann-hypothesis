import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor
import ReciprocityTheory.AnalyticForms.RegularLocalRings.SchemeRes
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjLogResCOfCR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem pC_eq_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    pC P = Ideal.map (MvPolynomial.map (Int.castRingHom ℂ)) P := rfl

theorem resExists_of_projLogRes (hL : ReciprocityTheory.AnForm.R.ProjLogResC) (hQ : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (h1 : PCRadicalStatement) (h2 : PCEquidimStatement) (h3 : PCMinContractStatement)
    (h4 : JacNotInPStatement) (h5 : PCContractStatement) : ResExistsStatement := by
  intro K _ ι _ P J e hP hJ hJP
  have hK : Nonempty K := hP.1
  have hprime : P.IsPrime := hP.2.1.1
  have hPhom : IsMultiHomogIdeal P := hP.2.1.2.1
  obtain ⟨s, G, hGhom, hGspan, hminor⟩ := h4 K ι P e hP
  set c := Fintype.card (Σ k, ι k) - (e + Fintype.card K) with hc
  set Jac : Ideal (MRing ι) := Ideal.span (jacMinors G c) with hJac
  have hJacHom : IsMultiHomogIdeal Jac := by
    refine ⟨jacMinors G c, ?_, rfl⟩
    rintro f ⟨a, b, rfl⟩
    exact isMultiHomog_det_pderiv G hGhom a b
  have hJ'hom : IsMultiHomogIdeal (J * Jac) := isMultiHomogIdeal_mul hJ hJacHom
  have hJ'P : ¬ J * Jac ≤ P := by
    intro h
    rcases hprime.mul_le.mp h with h1' | h1'
    · exact hJP h1'
    · exact hminor h1'
  refine ⟨J * Jac, Ideal.mul_le_left, hJ'hom, hJ'P, ?_⟩
  have hGC : ∀ i, ∃ a, ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) (G i)) a := by
    intro i
    obtain ⟨a, ha⟩ := hGhom i
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  have hspanC : Ideal.span (Set.range fun i => map (Int.castRingHom ℂ) (G i)) = pC P := by
    rw [pC_eq_map, ← hGspan, Ideal.map_span, ← Set.range_comp]
    rfl
  have hsing : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ),
      (∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC P) p, eval z h = 0) →
      ¬ IsRegularLocalRing (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC P) p) z) →
      ∀ f ∈ pC (J * Jac), eval z f = 0 := by
    intro p z hz hnreg f hf
    have hminC : ∀ (a : Fin c → Fin s) (b : Fin c → Σ k, ι k),
        eval z (Matrix.det (Matrix.of fun i j =>
          pderiv (b j) (map (Int.castRingHom ℂ) (G (a i))))) = 0 := by
      intro a b
      by_contra hne
      exact hnreg (ReciprocityTheory.AnForm.R.isRegularLocalRing_locAt_chart (pC P) e (h2 K ι P e hP)
        (fun i => map (Int.castRingHom ℂ) (G i)) hGC hspanC p z hz a b hne)
    have hle : pC (J * Jac) ≤ RingHom.ker (eval z : MRingOver ℂ ι →+* ℂ) := by
      rw [pC_eq_map, Ideal.map_mul]
      refine le_trans Ideal.mul_le_right ?_
      rw [hJac, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨d, ⟨a, b, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.map_det]
      have hmat : (MvPolynomial.map (Int.castRingHom ℂ)).mapMatrix
          (Matrix.of fun i j => pderiv (b j) (G (a i))) =
          Matrix.of fun i j => pderiv (b j) (map (Int.castRingHom ℂ) (G (a i))) := by
        ext i j
        simp [pderiv_map]
      rw [hmat]
      exact hminC a b
    exact RingHom.mem_ker.mp (hle hf)
  have hcomp : ∀ Q ∈ (pC P).minimalPrimes, ReciprocityTheory.AnForm.R.IsRelevant Q →
      ¬ pC (J * Jac) ≤ Q := by
    intro Q hQ _ hle
    apply hJ'P
    rw [← h3 K ι P e hP Q hQ]
    exact le_trans Ideal.le_comap_map (Ideal.comap_mono hle)
  have hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ),
      (∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC P) p, eval z h = 0) →
      ringKrullDim (ReciprocityTheory.AnForm.R.locAt (ReciprocityTheory.AnForm.R.chartIdeal (pC P) p) z) = e :=
    fun p z hz => ReciprocityTheory.AnForm.R.ringKrullDim_locAt_chart (pC P) (isMultiHomogIdeal_pC hPhom) e
      (h2 K ι P e hP) p z hz
  obtain ⟨R⟩ := ReciprocityTheory.AnForm.R.algRes_of_logResStC hQ (pC P) (pC (J * Jac)) e
    (isMultiHomogIdeal_pC hPhom) (h1 K ι P e hP) (isMultiHomogIdeal_pC hJ'hom) hcomp hsing hdim
    (hL K ι (pC P) (pC (J * Jac)) (isMultiHomogIdeal_pC hPhom) (isMultiHomogIdeal_pC hJ'hom)
      (h1 K ι P e hP) hsing hcomp)
  exact nonempty_anLogRes_of_algRes P (J * Jac) e hJ'hom hJ'P (h5 K ι P e hP) R

theorem resExists (hC : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStCR.{0}) (hQ : ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
    (h1 : PCRadicalStatement) (h2 : PCEquidimStatement) (h3 : PCMinContractStatement)
    (h4 : JacNotInPStatement) (h5 : PCContractStatement) : ResExistsStatement :=
  resExists_of_projLogRes (ReciprocityTheory.AnForm.R.projLogResC_of_CR hC hQ) hQ h1 h2 h3 h4 h5

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section
namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem poincareLelong_of_resolution (hE : ResExistsStatement) (hB : ResBridgeStatement)
    (hPL : ReciprocityTheory.AnForm.M.PoincareLelongStatement) (hPush : ResDivPushStatement) : ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution_atlas hE hB hPL ReciprocityTheory.AnForm.M.sncInducedAtlas hPush

theorem stokes_of_resolution (hE : ResExistsStatement) (hB : ResBridgeStatement) : StokesStatement :=
  stokes_of'' hE hB ReciprocityTheory.AnForm.M.byPartsSymm

theorem poincareLelong_of_resolution_pushforward (hE : ResExistsStatement) (hB : ResBridgeStatement) (hPush : ResDivPushStatement) :
    ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution hE hB ReciprocityTheory.AnForm.M.poincareLelong hPush

end ReciprocityTheory.ChartRestriction.G.Geo
end

section
namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem resExists_of_hironaka (h : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC ∧ ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE) :
    ResExistsStatement :=
  resExists_of_projLogRes (ReciprocityTheory.AnForm.R.projLogResC_of_C h.1 h.2) h.2 pcRadical pcEquidim pcMinContract
    jacNotInP pcContract

section

variable (h : ReciprocityTheory.AnForm.R.FinalTheorems.GFLogStC ∧ ReciprocityTheory.AnForm.R.FinalTheorems.FinTypeQE)
include h

theorem stokes_of_hironaka : StokesStatement :=
  stokes_of_resolution (resExists_of_hironaka h) resBridge

theorem poincareLelong_of_hironaka (hPush : ResDivPushStatement) : ArithmeticPoincareLelongFormula :=
  poincareLelong_of_resolution_pushforward (resExists_of_hironaka h) resBridge hPush

end

end ReciprocityTheory.ChartRestriction.G.Geo
end
