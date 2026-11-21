import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.OrbitAdmissibleOfSplitBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsStandardBasesLatticeAtPlaceOfAdaptedBases
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtLinAdaptedCoefEqStandardSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubstUnitaryLogarithmicCoordinates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CombOfTied
import Development.AutomorphicArithmetic.OrbitLabellings.LatticePairsOddDegreeIsometric

section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ γ : Fin r → (OrbitPlaces.Pl D × Fin N × Fin N') → MaximalUnramifiedExtension p, (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) ∧ (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.unitary_of_orthonormal | exact GlobalTheory.KerStd.unitary_of_orthonormal | (intros; apply GlobalTheory.KerStd.unitary_of_orthonormal <;> assumption)
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

noncomputable section

namespace GlobalTheory.KerStd.OneLetter

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)

theorem localLogarithm_eq_single_variable_oneLetter (D : D7) (p : ℕ) [Fact p.Prime] (h1 : nP D p = 1) {β : Type} (v : OrbitPlaces.Pl D × β) :
    OrbitPlaces.logPl D p v = at1 v (lgF ℂ_[p] p) := by
  rw [Formalism.L2.Th1.D.SingleLetterLog.at_variable_artin_hasse_eq_one_log]
  ext m
  have hb : ∀ e : ℕ, OrbitPlaces.backPl D p v.1 e = v.1 := fun e => by
    simp [OrbitPlaces.backPl, h1, posPl_zero]
  show (∑ e ∈ Finset.range (JetTdeg m + 1), _) = ∑ e ∈ Finset.range (m.degree + 1), _
  have hd : JetTdeg m = m.degree := rfl
  rw [hd]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [hb]

theorem owOK_one {K : Type} [NormedField K] (σ : K →+* K) :
    OwOK 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) :=
  ⟨fun _ => ⟨by simp, by simp⟩, fun _ => ⟨Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2, Formalism.L2.Th1.D.SingleLetterLog.iter_one σ 2⟩⟩

theorem trDual_one {K : Type} [NormedField K] (σ : K →+* K) :
    TrDual 2 σ (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) := by
  refine ⟨by simp, fun r r' => ?_⟩
  have hr : r = r' := Fin.ext (by have := r.isLt; have := r'.isLt; omega)
  rw [Formalism.L2.Th1.D.SingleLetterLog.univ_two, Finset.sum_pair (by decide)]
  have h1 : (1 : ZMod 2).val = 1 := rfl
  simp [h1, hr]

theorem beMean_fin_unit {K : Type} [Field K] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) (ζ : K) :
    Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) ζ =
      Formalism.L2.Th1.D.beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) ζ := by
  have h : Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Fin (2 / 2) => (1 : K)) (fun _ => 1) =
      Formalism.L2.Th1.D.beTil (d := 2) l σ be0 (fun _ : Unit => (1 : K)) (fun _ => 1) := by
    unfold Formalism.L2.Th1.D.beTil
    rw [Finset.sum_const, Finset.sum_const]
    simp
  unfold Formalism.L2.Th1.D.beMean
  rw [h]

end GlobalTheory.KerStd.OneLetter

namespace GlobalTheory.KerStd

open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open OneLetter

theorem expShape_of_integralClass : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  intro D p _ g2 g3 s2 ε σ F hC h1 N N' ep Th hep hH
  obtain ⟨h5, hg2, hg3, hε, hth, hσ, hF, hN⟩ := hC
  have hl : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨f1, f2, hph⟩ := Formalism.L2.Th1.D.FAux.ffs p Formalism.L2.Th1.D.first_level_on_curve g2 g3 ε hg2 hg3 hε hth σ hσ F hF s2 hN
  obtain ⟨ζ, hζ⟩ := Formalism.L2.Th1.D.FAux.exists_root2 p
  set B : MvPowerSeries (ZMod 2) (MaximalUnramifiedExtension p) :=
    Formalism.L2.Th1.D.beMean (d := 2) p σ (cob F (phFF p g2 g3 s2 ε)) (fun _ : Unit => (1 : MaximalUnramifiedExtension p)) (fun _ => 1) ζ with hBdef
  set Bc : MvPowerSeries (ZMod 2) ℂ_[p] := MvPowerSeries.map (MaximalUnramifiedExtension p).subtype B with hBc
  have hstd : BeStd p 2 Bc := ⟨σ, F, cob F (phFF p g2 g3 s2 ε), fun _ => 1, fun _ => 1, ζ,
    ⟨hσ, hF, f1, f2, owOK_one σ, trDual_one σ, hζ⟩, by rw [beOf, beMean_fin_unit]⟩
  have hB14 := GlobalTheory.T.standard_series_b_conditions_large_prime p 2 Bc h5 le_rfl even_two hstd

  have hO := Formalism.L2.Th1.D.oneLetterHalf (MaximalUnramifiedExtension p) p σ hσ F hF _ f1 f2 ζ hζ _ hph
  have h2 := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq (MaximalUnramifiedExtension p) ℂ_[p] Unit (MaximalUnramifiedExtension p).subtype (Formalism.L2.Th1.D.FAux.norm_coe p)).1 _ _ hO
  have hsL0 : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsL : MvPowerSeries.HasSubst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have e2 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (MvPowerSeries.C ((2 : MaximalUnramifiedExtension p)⁻¹) *
      MvPowerSeries.subst (fun _ : ZMod 2 => (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p))) B) =
      MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => (lgF ℂ_[p] p : MvPowerSeries Unit ℂ_[p])) Bc := by
    rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_subst hsL0, map_inv₀, map_ofNat]
    have e3 : MvPowerSeries.map (MaximalUnramifiedExtension p).subtype (lgF (MaximalUnramifiedExtension p) p : MvPowerSeries Unit (MaximalUnramifiedExtension p)) = lgF ℂ_[p] p :=
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF (MaximalUnramifiedExtension p).subtype p
    simp only [e3, hBc]
  rw [e2] at h2
  obtain ⟨-, hsymm, -, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] (OrbitPlaces.Pl D × Fin N × Fin N')
  have hsub := (Formalism.InvariantFactorPaths.G7.Top.simeqRules ℂ_[p] Unit).2.2.2.2 (OrbitPlaces.Pl D × Fin N × Fin N')
  have h3 : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', Simeq (at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)))
      (MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc) := by
    intro x
    have hsx : MvPowerSeries.HasSubst
        (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have h4 := hsub _ _ (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (fun _ => by simp) (fun _ => Formalism.InvariantFactorPaths.G7.TwoS.integral_X x) h2
    rw [MvPowerSeries.subst_mul hsx, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply hsL hsx] at h4
    exact h4
  have h5s := Formalism.L2.Th1.D.B4.simeq_sum Finset.univ _ _ fun x _ => h3 x
  obtain ⟨h50, h5I⟩ := hsymm _ _ h5s
  set f : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', at1 x (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) with hf
  set g : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ∑ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.C ((2 : ℂ_[p])⁻¹) *
        MvPowerSeries.subst (fun _ : ZMod 2 => at1 x (lgF ℂ_[p] p)) Bc with hg
  have hm0 : PowerSeries.constantCoeff (PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε)) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, Formalism.L2.Th1.D.FAux.cc_phFF hl, map_zero]
  have hf0 : MvPowerSeries.constantCoeff f = 0 := by
    rw [hf, map_sum]
    exact Finset.sum_eq_zero fun x _ => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero x hm0
  have hg0 : MvPowerSeries.constantCoeff g = 0 := by
    have h := h50
    rw [map_sub, hf0, sub_zero] at h
    exact h
  have hng0 : MvPowerSeries.constantCoeff (-g) = 0 := by rw [map_neg, hg0, neg_zero]
  have hnf0 : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf0, neg_zero]

  have hsA : MvPowerSeries.HasSubst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)
  have hsE : MvPowerSeries.HasSubst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
      (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun v => by simp
  have hlogfun : (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) =
      fun v => MvPowerSeries.C ep * at1 v (lgF ℂ_[p] p) := funext fun v => by rw [localLogarithm_eq_single_variable_oneLetter D p h1]
  have hlog2 : (OrbitPlaces.logPl D p (β := Fin N × Fin N')) = fun v => at1 v (lgF ℂ_[p] p) :=
    funext fun v => localLogarithm_eq_single_variable_oneLetter D p h1 v
  have hS : MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => MvPowerSeries.C ep * OrbitPlaces.logPl D p v) Th =
      MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
    rw [hlogfun, MvPowerSeries.subst_comp_subst_apply hsE hsA]
    congr 1
    funext v
    rw [MvPowerSeries.subst_mul hsA, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsA]

  have hE : ∀ z : OrbitPlaces.Pl D, ∀ a : Fin N, ∀ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc =
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc := by
    intro z a b
    simp only [map_one, one_mul, ite_self]
  have hsX : ∀ x : OrbitPlaces.Pl D × Fin N × Fin N', MvPowerSeries.HasSubst
      (fun _ : ZMod 2 => (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) :=
    fun x => MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => by simp
  set E' : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p] :=
    ((-1 : ℂ_[p]) / 2) • ∑ x : OrbitPlaces.Pl D × Fin N × Fin N',
      MvPowerSeries.subst (fun _ : ZMod 2 =>
        (MvPowerSeries.X x : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Bc with hE'
  have hsubE : MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p)) E' = -g := by
    rw [hE', ← MvPowerSeries.coe_substAlgHom hsA, map_smul, MvPowerSeries.coe_substAlgHom hsA,
      Formalism.L2.Th1.D.Pair.subst_sum hsA, hg, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.subst_comp_subst_apply (hsX x) hsA]
    simp only [MvPowerSeries.subst_X hsA]
    rw [← neg_mul, ← map_neg]
    congr 2
    ring
  have hE0 : MvPowerSeries.constantCoeff E' = 0 := by
    rw [← HostLog.constantCoeff_subst (fun i => Formalism.L2.Th1.D.Pair.constantCoeff_inVar_eq_zero i (Formalism.L2.Th1.D.Pair.cc_lgF hl)) E',
      hsubE, hng0]
  have hsum : (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc) = E' := by
    simp only [hE, hE', Fintype.sum_prod_type, Finset.smul_sum]
  have e5 : mvExp (g - f) * mvExp (-g) = mvExp (-f) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add h50 hng0]
    congr 1
    ring
  have e6 : mvExp (-f) * mvExp f = 1 := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add hnf0 hf0, neg_add_cancel, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.mvExp_zero']
  refine ⟨ep, hep, fun _ => Bc, fun _ => hB14, fun _ => 1, fun _ => norm_one, fun _ => -1, fun _ => Or.inr rfl,
    mvExp (g - f) * (mvExp f * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th)),
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' h5I hH, ?_⟩
  show _ = _ * MvPowerSeries.subst (OrbitPlaces.logPl D p (β := Fin N × Fin N')) (product_zeroth_first_parts.expS ℂ_[p]
    (∑ z : OrbitPlaces.Pl D, ((-1 : ℂ_[p]) / 2) • ∑ a : Fin N, ∑ b : Fin N',
      MvPowerSeries.subst (fun s : ZMod 2 => if s = 0 then
          (MvPowerSeries.X (z, a, b) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])
        else MvPowerSeries.C (1 : ℂ_[p]) * MvPowerSeries.X (z, a, b)) Bc))
  rw [hS, hsum, hlog2]
  show _ = _ * MvPowerSeries.subst _ (mvExp E')
  rw [Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hsA hE0, hsubE]
  calc _ = (mvExp (-f) * mvExp f) * MvPowerSeries.subst (fun i : OrbitPlaces.Pl D × Fin N × Fin N' => at1 i (lgF ℂ_[p] p))
        (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' =>
          (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th) := by
        rw [e6, one_mul]
    _ = _ := by rw [← e5]; ring

end GlobalTheory.KerStd
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentShape_of_integralClass_oneLetter : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → nP D p = 1 → ∀ (N N' : ℕ) (ep : ℂ_[p]) (Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]), ‖ep‖ = 1 → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C ep * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) Th : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) → OrbitPlaces.ThetaExpansionRealPlaces D p Th := by
  atlas_forward_decl GlobalTheory.KerStd.expShape_of_integralClass
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem nP_eq_one_of_hP_eq_zero (D : D7) (p : ℕ) (hC : IsResidueClassZero D p) (h0 : hP D p = 0) : nP D p = 1 := by
  have hS : ¬ IsSg D p := by
    intro hs
    unfold IsResidueClassZero at hC
    unfold IsSg at hs
    rw [hC] at hs
    exact absurd hs (by decide)
  unfold nP
  rw [if_neg hS, h0, addOrderOf_zero]

theorem thetaExpansionRealPlaces_stdSer_of_adm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  intro D cc δ B χ p _ lam hHost h5 hC hP0 N N' L L' P P' hAdm hS hS' G hG
  obtain ⟨c, g2, g3, s2, ε, σ, F, hc, hcd, hfam⟩ := hHost
  obtain ⟨r, b, hLB, hON, hInt⟩ := hfam N N' L L' hAdm
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces D p lam σ hcd.2.2.2.2.2.1 h5 hC hP0 N N' L L' P P' hAdm hS hS' r b hLB hON
  have hU := GlobalTheory.T.subst_unitary_logarithmic_coordinates p g2 g3 s2 ε σ F hcd (Fin r) (OrbitPlaces.Pl D × Fin N × Fin N') γ hγ1 (by convert hγ2) _ (hInt G hG)
  rw [← hγ3 c G] at hU
  exact GlobalTheory.T.exponentShape_of_integralClass_oneLetter D p g2 g3 s2 ε σ F hcd (nP_eq_one_of_hP_eq_zero D p hC hP0) N N' c _ hc hU

end GlobalTheory.KerStd
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExpansionRealPlaces_stdSer_of_adm' : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), HostAt B χ p lam → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ G, IsComb D B.tor (B.eNat χ) lam L L' G → OrbitPlaces.ThetaExpansionRealPlaces D p (stdSer D lam (fun _ => 1) P P' G) := by
  atlas_forward_decl GlobalTheory.KerStd.thetaExpansionRealPlaces_stdSer_of_adm
end

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.Ggeo

theorem frobeniusConjugation_conditions_adaptedKernelDatum_alt : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  intro hAlg hHost D L hT Gi Gl K Y cX ex t hHyp hAd h3 ep be sg
  have main : ∀ u μ (w : D.what₂.places.Pl), LevFree Y u μ w → IsResidueClassZero D (D.what₂.places.resChar w) → ∀ i < D.R.m, ∀ c c',
      ∀ Q : MvPowerSeries (OrbitPlaces.Pl D × Fin (D.R.N i) × Fin (D.R.N (i + 1))) ℂ_[D.what₂.places.resChar w] → Prop,
      (HostAt t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) → 5 ≤ D.what₂.places.resChar w →
        ∀ (L : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin (D.R.N (i + 1)) → D.host.E))
          (P : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E)
          (P' : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.host.E),
          admitted D (D.R.N i) (D.R.N (i + 1)) L L' → StdBases D (t.ent.lam w) L P → StdBases D (t.ent.lam w) L' P' →
          ∀ G, IsComb D t.B.tor (t.B.eNat t.χ) (t.ent.lam w) L L' G → Q (stdSer D (t.ent.lam w) (fun _ => 1) P P' G)) →
      Q (t.ent.Th u μ w i c c') := by
    intro u μ w hLF' hC i hi c c' Q hQ
    have hprime : (D.what₂.places.resChar w).Prime := Fact.out
    have h5 : 5 ≤ D.what₂.places.resChar w := (DIV.Inh.orbit_admissible_of_split_bound D h3).2 _ hprime hC
    have hAdPl : Formalism.L2.Ker.AdPl D w := Or.inl hC
    obtain ⟨Pm, hB, -, hConj, hTh⟩ := hAd w hAdPl u μ hLF'
    obtain ⟨hAdm, hComb⟩ := GlobalTheory.Ggeo.KerComb.comb_of_tied hAlg D L hT Gi Gl K Y cX ex t hHyp u μ w hLF' i hi c c'
    have hHA := hHost D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) (t.ent.lam w) h5 (Or.inl hC)
    have hS : StdBases D (t.ent.lam w) ((t.O u μ).lat i c).1 (Pm i c) :=
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat i c).2.1 (fun τ => hB i hi.le c τ)
        (fun τ τ' h => hConj i hi.le c τ τ' h)
    have hS' : StdBases D (t.ent.lam w) ((t.O u μ).lat (i + 1) c').1 (Pm (i + 1) c') :=
      GlobalTheory.T.isStandardBasesLatticeAtPlace_of_adapted_bases D _ (t.ent.lam w) _ _ _ ((t.O u μ).lat (i + 1) c').2.1 (fun τ => hB (i + 1) hi c' τ)
        (fun τ τ' h => hConj (i + 1) hi c' τ τ' h)
    have key := hQ hHA h5 _ _ _ _ hAdm hS hS' _ hComb
    rw [hTh i hi c c', GlobalTheory.T.atLin_adaptedCoef_eq_standardSeries]
    exact key
  refine ⟨fun u μ w hLF hC hP0 i hi _ c c' => ?_, fun u μ w hLF hC i hi _ c c' => ?_⟩
  · exact main u μ w hLF hC i hi c c' (OrbitPlaces.ThetaExpansionRealPlaces D (D.what₂.places.resChar w)) fun hHA h5 =>
      GlobalTheory.T.thetaExpansionRealPlaces_stdSer_of_adm' D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC hP0 _ _
  · have hodd : Odd (nP D (D.what₂.places.resChar w)) := by
      have hs : ¬ IsSg D (D.what₂.places.resChar w) := fun h => by
        have h1 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.inertClass := hC.1
        have h2 : D.host.cls (D.what₂.places.resChar w) = PrimeClass.signal := h
        rw [h1] at h2; cases h2
      unfold nP
      rw [if_neg hs]
      exact hC.2.1
    exact main u μ w hLF hC.1 i hi c c' (OrbitPlaces.EvenConditionsAllReal D (D.what₂.places.resChar w)) fun hHA h5 =>
      UpperTheory.lattice_pairs_odd_degree_isometric D t.cc t.δ t.B t.χ (D.what₂.places.resChar w) (t.ent.lam w) hHA h5 hC.1 hodd _ _

end GlobalTheory.Ggeo
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusConjugation_conditions_adaptedKernelDatum : Formalism.L2.KerInert.AlgTAll → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), 5 ≤ p → (IsResidueClassZero D p ∨ IsSg D p) → HostAt B χ p lam) → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : Formalism.L2.Ker.KerEntTied ex), t.Hyp → t.Adapted → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.EvenConditionsAtC (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  atlas_forward_decl GlobalTheory.Ggeo.frobeniusConjugation_conditions_adaptedKernelDatum_alt
end
