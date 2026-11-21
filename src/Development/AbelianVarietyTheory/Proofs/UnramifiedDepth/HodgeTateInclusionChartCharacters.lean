import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapPderiv
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNilpotentGroupChartSmoothCommGroupStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtension
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UniformizationSplitFormalGroupLawEquivariant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsHodgeTateDatumPolarisedAbelianCharacters
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NilChartOfIsChartJ
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowerSeriesReadingGroupHomNilpotentChartsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private lemma smul_mem_span_of_split {O κ : Type} [CommRing O] [Fintype κ] [DecidableEq κ] {g d r m : ℕ}
    (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (Ht : Matrix (Fin g) κ O)
    (s : Fin m → Fin d → O) (cp : O) (hex : SplitEx A B)
    (hB : ∀ i, ∃ k, s k = Bᵀ *ᵥ (fun l => Ht l i)) (hT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1)
    (hsurj : ∀ f : Fin g → O, ∃ t, Ht *ᵥ t = cp • f) (f : Fin d → O) :
    cp • f ∈ Submodule.span O (Set.range s) := by
  obtain ⟨-, A', B', -, -, h1⟩ := hex
  choose k hk using hT
  set u : Fin d → O := ∑ i, (Aᵀ *ᵥ f) i • s (k i) with hu
  have huS : u ∈ Submodule.span O (Set.range s) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k i, rfl⟩)
  have hAu : Aᵀ *ᵥ u = Aᵀ *ᵥ f := by
    rw [hu, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hk]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : Aᵀ *ᵥ (f - u) = 0 := by rw [Matrix.mulVec_sub, hAu, sub_self]
  have h2 : A'ᵀ * Aᵀ + Bᵀ * B'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add, h1, Matrix.transpose_one]
  have h3 : f - u = Bᵀ *ᵥ (B'ᵀ *ᵥ (f - u)) := by
    have := congrArg (fun M => M *ᵥ (f - u)) h2
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, zero_add,
      Matrix.one_mulVec] at this
    exact this.symm
  obtain ⟨t, ht⟩ := hsurj (B'ᵀ *ᵥ (f - u))
  have h4 : cp • (f - u) = Bᵀ *ᵥ (Ht *ᵥ t) := by rw [ht, Matrix.mulVec_smul, ← h3]
  have h5 : Ht *ᵥ t = ∑ i, t i • (fun l => Ht l i) := by
    ext l
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have h6 : cp • (f - u) ∈ Submodule.span O (Set.range s) := by
    rw [h4, h5, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Matrix.mulVec_smul]
    obtain ⟨j, hj⟩ := hB i
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj⟩)
  have h7 : cp • f = cp • (f - u) + cp • u := by rw [← smul_add, sub_add_cancel]
  rw [h7]
  exact Submodule.add_mem _ h6 (Submodule.smul_mem _ _ huS)

theorem linDat_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL c hc f
  have := htd_domain hS
  obtain ⟨hEt, hdiag, hdet⟩ := htd_E H
  have hsurj := ht_cp_surj H.Ht H.Bt _ cp hEt hdiag hdet (htd_cp_ne hS) H.form_eq_alt
  have hle : v (algebraMap O C c) ≤ v (algebraMap O C cp) := by
    rw [← hS.cp_val] at hc
    exact le_of_pow_le_pow_left₀ (by have := (Fact.out : p.Prime).two_le; omega) zero_le hc
  obtain ⟨e, rfl⟩ := hv.dvd_of_le hle
  rw [mul_comm, mul_smul]
  exact Submodule.smul_mem _ _
    (smul_mem_span_of_split A B H.Ht s cp hL.exact hL.fromB hL.fromT hsurj f)

end GlobalTheory.ChF
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearData_hodgeTate_inclusion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) → ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range s) := by
  atlas_forward_decl GlobalTheory.ChF.linDat_hodgeTate_inclusion
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem eq_intCast_of_conj {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {g : ℕ}
    (ρ : (ℤ_[p] ⊗[ℤ] ℤ) →+* Matrix (Fin g) (Fin g) O) (S M : Matrix (Fin g) (Fin g) O) (hS : IsUnit S) (a : ℤ)
    (h : M * S = S * ρ (1 ⊗ₜ[ℤ] a)) : M = (a : Matrix (Fin g) (Fin g) O) := by
  have h1 : ((1 : ℤ_[p]) ⊗ₜ[ℤ] a) = ((a : ℤ) : ℤ_[p] ⊗[ℤ] ℤ) := by
    rw [← Algebra.TensorProduct.includeRight_apply]; simp
  rw [h1, map_intCast] at h
  obtain ⟨u, rfl⟩ := hS
  rw [← (Int.cast_commute a (u : Matrix (Fin g) (Fin g) O)).eq] at h
  exact (Units.mul_left_inj u).mp h

private theorem mul_intCast_eq {O : Type} [CommRing O] {m n : ℕ} (M : Matrix (Fin m) (Fin n) O) (a : ℤ) :
    M * (a : Matrix (Fin n) (Fin n) O) = (a : Matrix (Fin m) (Fin m) O) * M := by
  ext i j
  simp [Matrix.mul_apply, Matrix.intCast_apply, mul_comm]

theorem hodgeTate_inclusion_chart : ∀ (p : ℕ) [Fact p.Prime], HTFSt p := by
  intro p _ T _ _ _ _ _ _ hp G _ _ D A x d F xx hC C _ _ _ v O _ _ hv _ _ iota hiota
  obtain ⟨hL1, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨-, -, -, -, -, -, hcube, -⟩ := hL1
  letI : Algebra ℤ_[p] O := ((GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1).some
  have hFH : FH p (F.mapF iota) := by
    have h := GlobalTheory.FormalTorsion.fhSt p
    unfold FHSt at h
    unfold FH
    intro m
    obtain ⟨h1, h2, -, h4⟩ := h T hp G D A x d F xx hC C v O hv iota hiota m
    exact ⟨h1, h2, h4⟩
  obtain ⟨X, hX, -⟩ := GlobalTheory.T.exists_nilChart_reads_of_isChartJ T G x.1 d F xx hC
  obtain ⟨FB, xB, hxB⟩ := GlobalTheory.T.exists_nilpotentGroupChart_smooth_commGroup T D.toPre.P.A D.toPre.P.g D.toPre.P.5
  obtain ⟨r, J, Q, hEx, -⟩ := GlobalTheory.T.uniformization_split_formal_group_law_equivariant T (IsLocalRing.maximalIdeal T) D A G x d D.toPre.P.g F FB X xB hX hxB
  obtain ⟨o, ho⟩ := GlobalTheory.exists_oAct_int hcube (Spec (CommRingCat.of T)) D.toPre.P
  have hα : ∀ a : ℤ, ∃ φ, Reads xB xB (o.act a) φ := fun a =>
    GlobalTheory.T.exists_powerSeries_reading_groupHom_nilpotentCharts T D.toPre.P.A D.toPre.P.A D.toPre.P.g D.toPre.P.g FB.F FB.F xB xB hxB hxB (o.act a)
      (by rw [ho a]; exact GlobalTheory.IntAct.isMonHom_id_zpow a)
  choose α hα using hα
  obtain ⟨hmapF, -, hmapEx⟩ := GlobalTheory.T.formalGroupLaw_jacobian_extension_changeCoeff T O iota
  obtain ⟨F', hF'⟩ := hmapF d F
  obtain ⟨FB', hFB'⟩ := hmapF D.toPre.P.g FB
  obtain ⟨cp, hUp, H, S, hP, hPL, hS, hSa, hSu⟩ :=
    GlobalTheory.T.exists_hodgeTateDatum_polarisedAbelian_characters p C v O hv T iota D.toPre.P D.toPre.P.g rfl ℤ o FB xB hxB α hα
  have hαB : ∀ a : ℤ, lin (fun j => MvPowerSeries.map iota (α a j)) =
      (a : Matrix (Fin D.toPre.P.g) (Fin D.toPre.P.g) O) := fun a =>
    eq_intCast_of_conj H.ρL S _ hS a (hSa a)
  obtain ⟨cp', hUp', H', B, m, u, hu, hLin⟩ :=
    GlobalTheory.T.exists_linearData_of_split_formalGroup_extension p C v O hv ℤ d D.toPre.P.g r F' FB' (fun j => MvPowerSeries.map iota (J j))
      (fun j => MvPowerSeries.map iota (Q j)) (by rw [hF', hFB']; exact hmapEx d D.toPre.P.g r F FB J Q hEx)
      (by rw [hF']; exact hFH) (Int.castRingHom _) (Int.castRingHom _)
      (fun a j => MvPowerSeries.map iota (α a j))
      (fun a => by rw [hαB a, eq_intCast]; exact mul_intCast_eq _ a)
      (fun a => by
        have e : ((a : Matrix (Fin r) (Fin r) ℤ)).map (Int.castRingHom O) = (a : Matrix (Fin r) (Fin r) O) :=
          map_intCast (Int.castRingHom O).mapMatrix a
        rw [eq_intCast, eq_intCast, e]
        exact (mul_intCast_eq _ a).symm)
      ⟨cp, hUp, H, S, hP, hPL, hS, hSa, by rw [hFB']; exact hSu⟩
  refine ⟨m, u, fun k => hF' ▸ hu k, ?_⟩
  intro c hc f
  exact GlobalTheory.T.linearData_hodgeTate_inclusion p C v O hv ℤ cp' hUp' D.toPre.P.g H' d r m _ B (Int.castRingHom _) (Int.castRingHom _)
    (fun k => dl (u k)) hLin c hc f

end GlobalTheory.ChF
end
