module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

noncomputable section

namespace GlobalTheory.LiftChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG



theorem charAt (D : D7) (cf : CharFrame D) (C : CharSide D cf) (j : Fin D.R.m) :
    ∃ μ : D.naut.CG 1, (C.e1 μ).1 = cf.mu0 j ∧ D.naut.csd μ ∧
      (∀ w, ¬ IsSplitPl D.host w → D.naut.unr (D.naut.locG μ w) ∧ D.naut.unr (D.naut.locG D.naut.etaTinv w)) ∧
      ∀ τ, D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧
        D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have hm := cf.isMu0 j
  refine ⟨C.e1.symm ⟨cf.mu0 j, hm.unitary⟩, by simp, ?_, ?_, ?_⟩
  · rw [C.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ hm.triv
  · intro w hw
    refine ⟨(C.unr_iff _ w).2 ?_, (C.unr_iff _ w).2 ?_⟩
    · rw [Equiv.apply_symm_apply]
      refine hm.unr w fun k hk => hw ?_
      exact (Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1
    · rw [C.etaTinv]
      intro x hx
      have := cf.isEta.unr w x hx
      show ((cf.eta.loc w) x)⁻¹ = 1
      rw [this, inv_one]
  · have hinf : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) (fun _ => -(1/2 : ℚ)) := by
      rw [C.etaTinv]
      refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
      have h := cf.isEta.inf k
      show (((cf.eta.inf k)⁻¹ : ℂˣ) : ℂ) = _
      rw [Units.val_inv_eq_inv_val, h]
      simp only [zpow_one, zpow_neg_one, Finset.prod_inv_distrib]
    intro τ
    obtain ⟨h1, h2⟩ := C.infG _ _ hinf (D.eTau τ)
    refine ⟨?_, ?_⟩
    · show D.naut.infG _ (embPsi D.host (D.eTau τ)) = _
      rw [h1]
      congr 1
      push_cast
      ring
    · show D.naut.infG _ ((starRingEnd ℂ).comp (embPsi D.host (D.eTau τ))) = _
      rw [h2]
      congr 1
      push_cast
      ring

end GlobalTheory.LiftChar

end
