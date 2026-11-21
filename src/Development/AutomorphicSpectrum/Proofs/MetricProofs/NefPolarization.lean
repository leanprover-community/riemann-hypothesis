import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XContract
import BuildAid.ForwardExisting
import Development.WeilBound.CoreStatements.PluriharmonicCharts.X_deg_generic
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XNefCurve
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibility

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem varieties_over_rat_arith_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P :=
  @PositivityTheory.Xgp.t_contract

end GlobalTheory.CompanionTheory.Ar.PB
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_variety_generic_fibre_projective : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.varieties_over_rat_arith_contract
end

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem curvatureIntegral_eq_genericIntersection : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) :=
  @PositivityTheory.Xgp.t_deg_generic

end GlobalTheory.CompanionTheory.Ar.PB
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_intersection_equals_points_integral : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection
end

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem nonneg_degree_horizontal_curve : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 :=
  PositivityTheory.Xgp.t_nef_curve

end GlobalTheory.CompanionTheory.Ar.PB
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_degree_nonnegative_psh : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve
end

section
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem section_sub_degree : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 :=
  @PositivityTheory.Xgp.t_pol_sec

end GlobalTheory.CompanionTheory.Ar.PB
end

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lattice_shift_nonzero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (α : K → ℤ) (dβ : K → ℕ), (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1) 1, e ≠ 0) → ∃ k : ℕ, 1 ≤ k ∧ ∃ e ∈ chartLat y (fun κ => (k : ℤ) * α κ - 1 - dβ κ) 1, e ≠ 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PB.section_sub_degree
end

section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

theorem exists_ne_zero_of_relevant {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsRelevant (mCoordIdeal y)) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem fin_one_const {α : Type} (a : α) : (fun _ : Fin 1 => a) = ![a] := by
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

namespace GlobalTheory.CompanionTheory.Ar.PB

open GlobalTheory.CompanionTheory.Ar.PB.NefPolProof in

theorem nefPol : NefPol := by
  intro hIn D σ _ S Fl hFl K _ ι _ Ω _ _ y Re hJ hBir I hI n hn
  have hK : Nonempty K := Re.arith.1
  have hRe := GlobalTheory.T.realisation_potential_degree_compatibility hIn.resExists K ι D σ S (mCoordIdeal y) Re
  have hsm : IsSmoothHerm (combLine Re.ref n) := (hRe.2.2.2 n).1
  have hnef : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.NefOnF I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) (combLine Re.ref n).a := by
    intro W hW hle
    obtain ⟨hW', hWmap⟩ := (GlobalTheory.T.arithmetic_variety_generic_fibre_projective K ι 1).1 W hK hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
    have h0 := GlobalTheory.T.geometric_degree_nonnegative_psh hIn K ι D σ S (mCoordIdeal y) Re Fl hFl hJ n hn _ hW' hPW
    have h1 := GlobalTheory.T.generic_intersection_equals_points_integral hIn K ι I hI 1 (W.comap (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ => combLine Re.ref n) hW' (fun _ => hsm)
    rw [hWmap] at h1
    have h2 : (0 : ℝ) ≤ (I W 1 fun _ => (combLine Re.ref n).a : ℤ) := by
      rw [← h1]; exact h0
    rw [← fin_one_const]
    exact_mod_cast h2
  refine ⟨hnef, ?_⟩
  intro hpos β dβ _ _
  have hdeg := (hRe.2.2.2 n).2
  have hgp : 0 < geomDeg (mCoordIdeal y) (combLine Re.ref n) D := by
    rw [hdeg]
    exact mul_pos (by exact_mod_cast Re.deg_pos) hpos
  have h1 := GlobalTheory.T.generic_intersection_equals_points_integral hIn K ι I hI D (mCoordIdeal y) (fun _ => combLine Re.ref n) Re.arith (fun _ => hsm)
  have hI0 : 0 < I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) := by
    have : (0 : ℝ) < (I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) : ℤ) := by
      rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal, ← h1]; exact hgp
    exact_mod_cast this
  have hsec := hIn.siuZ K ι Ω y D (combLine Re.ref n).a I hI Re.arith hBir hnef hI0
  exact GlobalTheory.T.chart_lattice_shift_nonzero K ι Ω y (combLine Re.ref n).a dβ
    (exists_ne_zero_of_relevant y Re.arith.2.1.2.2) hsec

end GlobalTheory.CompanionTheory.Ar.PB
end
