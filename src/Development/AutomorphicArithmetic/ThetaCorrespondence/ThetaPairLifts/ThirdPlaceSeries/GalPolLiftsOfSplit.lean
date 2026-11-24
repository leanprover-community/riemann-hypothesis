module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepUniform
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.CuspRep GlobalTheory.WeilDeligne Polynomial
end GlobalTheory.GalAllPlaces
end
noncomputable section
namespace GlobalTheory.GalAllPlaces
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
theorem galPol_lpTw_mem_lifts_eventually : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → ∀ (K : Type) [Field K] (e : K →+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e) → ∀ᶠ w in Filter.cofinite, galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) ∈ Polynomial.lifts e := by
  intro hL hF hG hCh D T C K _ e π hc hr hsplit
  have ha : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  set P : HeightOneSpectrum (𝓞 D.host.E) → ℂ[X] :=
    fun w => galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2)) with hP
  have hU : ∀ᶠ w in Filter.cofinite, ((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w) :=
    (eventually_natCast_notMem D.host.E 2).and (D.naut.locG_unr_ae π)
  obtain ⟨ρ, hρc, hρ⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 ι ha π hc hr
  letI : Algebra K ℂ := e.toAlgebra
  have key : ∀ γ : ℂ ≃ₐ[K] ℂ, ∀ w, (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) →
      (P w).map (γ : ℂ →+* ℂ) = P w := by
    intro γ
    obtain ⟨ρ', hρ'c, hρ'⟩ := _root_.GlobalTheory.GalAllPlaces.exists_rep_uniform_alt_alt hL hF hG C 2 (ι.trans γ.toRingEquiv) ha π hc hr
    have hfix : ∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w :=
      hsplit.mono fun w hw hs => by
        obtain ⟨q, hq⟩ := (Polynomial.mem_lifts _).1 (hw hs)
        simp only [hP]
        rw [← hq, Polynomial.map_map]
        congr 1
        ext x
        exact γ.commutes x
    have hall := hU.and hfix
    rw [Filter.eventually_cofinite] at hall
    set S := hall.toFinset with hS
    have hmap : ∀ g, (((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map
        (ι.trans γ.toRingEquiv).toRingHom) = ((((ρ' g : GL (Fin D.R.r) (Qbar 2)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)).charpoly.map ι.toRingHom).map (γ : ℂ →+* ℂ)) := by
      intro g
      rw [Polynomial.map_map]
      rfl
    have heq := GlobalTheory.charpoly_eq_of_eqOn_dense
      (fun g => ((ρ g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2)))
      (fun g => ((ρ' g : GL (Fin D.R.r) (Qbar 2)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar 2))) hρc hρ'c _
      (GlobalTheory.ChebSplitDense.chebSplit_nd hCh D S) (by
        rintro g ⟨w, hwS, hsp, B, hB, hFr⟩
        have hw : (((2 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal ∧ D.naut.unr (D.naut.locG π w)) ∧
            (IsSplitPl D.host w → (P w).map (γ : ℂ →+* ℂ) = P w) := by
          by_contra h
          exact hwS (by rw [hS, Set.Finite.mem_toFinset]; exact h)
        apply Polynomial.map_injective ι.toRingHom ι.injective
        rw [hρ w hw.1.1 hw.1.2 B g hB hFr]
        apply Polynomial.map_injective (γ : ℂ →+* ℂ) γ.injective
        rw [← hmap, hρ' w hw.1.1 hw.1.2 B g hB hFr, hw.2 hsp])
    intro w hw
    obtain ⟨σ, hσ⟩ := exists_isFrob (D.nd.plOm.2 w)
    have h1 := hρ w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    have h2 := hρ' w hw.1 hw.2 _ σ (D.nd.plOm.2 w) hσ
    rw [hmap, ← heq σ, h1] at h2
    exact h2
  filter_upwards [hU] with w hw
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  exact GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv ((P w).coeff n) fun γ => by
    have := congrArg (fun p : ℂ[X] => p.coeff n) (key γ w hw)
    simpa [Polynomial.coeff_map] using this
end GlobalTheory.GalAllPlaces
end
end
