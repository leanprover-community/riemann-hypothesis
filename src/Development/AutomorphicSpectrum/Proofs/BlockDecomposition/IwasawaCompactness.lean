module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.LeftInvSect
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

theorem iwaCpt : IwaCpt := by
  intro D n C hC
  have hCK : IsCompact (C * (K D n : Set (G D n))⁻¹) := hC.mul isCompact_K.inv
  have hQ : IsCompact ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) :=
    (isClosed_P (D := D) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hCK
  have hL := hQ.image (continuous_leviBlock (D := D) (n := n))
  set L := leviBlock (D := D) (n := n) '' ((↑) ⁻¹' (C * (K D n : Set (G D n))⁻¹) : Set (P D n)) with hLdef
  have hR : Continuous fun a : GL (Fin n) (AE D) => (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_absE.comp continuous_detGL)
  obtain ⟨R, hRb⟩ := (hL.image hR).bddAbove
  refine ⟨Units.val '' L, (fun a : GL (Fin n) (AE D) => (a⁻¹).1) '' L, R, hL.image Units.continuous_val,
    hL.image Units.continuous_coe_inv, fun h hh => ?_⟩
  obtain ⟨q, hq, k, hk, rfl⟩ := Iwasawa.exists_mul D n h
  have hmem : leviBlock (D := D) (n := n) ⟨q, hq⟩ ∈ L :=
    ⟨⟨q, hq⟩, ⟨q * k, hh, k⁻¹, Set.inv_mem_inv.2 hk, by simp⟩, rfl⟩
  obtain ⟨m, t, b, e, hm, ht⟩ := exists_levi_unip hq (leviBlock (D := D) (n := n) ⟨q, hq⟩) rfl
  exact ⟨m, t, k, _, b, hk, by rw [e], hm, ht, ⟨_, hmem, rfl⟩, ⟨_, hmem, rfl⟩, hRb ⟨_, hmem, rfl⟩⟩

end GlobalTheory.CompanionTheory.ThTot

end
