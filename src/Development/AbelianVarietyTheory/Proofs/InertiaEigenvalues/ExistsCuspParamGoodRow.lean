module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

end GlobalTheory.RowCuspFromLift

end
