import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLatticeStatement

section
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem norm_le_of_qB_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M n : ℕ) (hM : 1 ≤ M) (z : ℚ_[l]) (hz : qB P z ∈ Lat AI M n) :
    ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  let J : ThetaL P AI := GlobalTheory.ThetaTie.thetaL T
  obtain ⟨a, ha⟩ := hz
  have hq : ∀ c : ℚ_[l], ‖J.θ (qB P c)‖ = ‖c‖ := by
    intro c
    have e : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ c
    rw [e, J.θ_Om]
    exact (PadicComplex.norm_extends _ _).trans (PadicAlgCl.norm_extends _ _)
  have h1 := FilB_anti (P := P) (a := 1) (b := (M : ℤ)) (by exact_mod_cast hM) ha
  have h0 := FilB_anti (P := P) (a := 0) (b := 1) (by norm_num) h1
  have hk := (J.θ_ker _ h0).2 h1
  have hadd := J.θ_add _ h0 _ (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  rw [sub_add_cancel, hk, zero_add] at hadd
  have e2 : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    simp only [map_mul, map_pow, map_natCast]
  rw [e2, J.θ_mul _ (qB_mem _) _ (io_mem AI a)] at hadd
  rw [← hq z, hadd, norm_mul, hq, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end GlobalTheory.ExpImage
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_qB_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M n : ℕ), 1 ≤ M → ∀ z : ℚ_[l], qB P z ∈ Lat AI M n → ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  atlas_forward_decl GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat
end

section
section
namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc Filter Topology

theorem exists_padicInt_lim {l : ℕ} [Fact l.Prime] (z : ℕ → ℤ_[l])
    (h : ∀ n m, n ≤ m → ‖z n - z m‖ ≤ (l : ℝ) ^ (-(n : ℤ))) :
    ∃ y : ℤ_[l], ∀ n : ℕ, ∃ w : ℤ_[l], y - z n = (l : ℤ_[l]) ^ n * w := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have h0 : Tendsto (fun n : ℕ => (l : ℝ) ^ (-(n : ℤ))) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (l : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ hl)
    simpa using this
  have hc : CauchySeq z :=
    cauchySeq_of_le_tendsto_0' _ (fun n m hnm => by rw [dist_eq_norm]; exact h n m hnm) h0
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨y, fun n => ?_⟩
  have h1 : ‖z n - y‖ ≤ (l : ℝ) ^ (-(n : ℤ)) :=
    le_of_tendsto ((tendsto_const_nhds.sub hy).norm)
      (eventually_atTop.2 ⟨n, fun m hm => h n m hm⟩)
  rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at h1
  exact h1

theorem nearZ_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (hM : 1 ≤ M) (v : P.R.BdR)
    (hv : ∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) : NearZ P M v := by
  choose z hz using hv
  obtain ⟨y, hy⟩ := exists_padicInt_lim z (fun n m hnm => by
    have h1 := sub_mem (hz n) (Lat_anti AI hnm (hz m))
    rw [sub_sub_sub_cancel_right, ← map_sub] at h1
    exact GlobalTheory.T.norm_le_of_qB_mem_Lat_alt l P AI T M n hM _ h1)
  refine ⟨y, GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice l P AI T M _ fun n => ?_⟩
  obtain ⟨w, hw⟩ := hy n
  have h2 := io_mem_Lat AI M n (algebraMap ℤ_[l] (Ainf l) w)
  rw [← map_natCast (algebraMap ℤ_[l] (Ainf l)), ← map_pow, ← map_mul, ← hw, io_zl AI T,
    PadicInt.coe_sub, map_sub] at h2
  have := add_mem h2 (hz n)
  rwa [sub_add_sub_cancel] at this

end GlobalTheory.ExpImage
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ), 1 ≤ M → ∀ v : P.R.BdR, (∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) → NearZ P M v := by
  atlas_forward_decl GlobalTheory.ExpImage.nearZ_of_forall_Lat
end
