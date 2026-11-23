module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType
open GlobalTheory.DepthZeroJac GlobalTheory.IwahoriInj GlobalTheory.StepData

theorem unipRad_points_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    unipRad k (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) = unipB k (Fin n) := by
  ext g
  rw [mem_unipB, mem_unipRad, mem_parab]
  simp only [blk, Equiv.sigmaUnique_symm_apply, Equiv.sigmaUnique_apply]
  refine and_congr Iff.rfl ⟨fun h i => (h i 0 0).trans (by simp), fun h a i j => ?_⟩
  rw [h a, Subsingleton.elim i j]
  simp

theorem eq_zero_of_fixed_KO_twKer_unipB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ v ∈ twKer π (unipB k (Fin n)) 1, (∀ g ∈ KO k (Fin n), π g v = v) → v = 0 := by
  intro k _ _ _ _ n V _ _ π hπ v h1 hfix
  rw [← unipRad_points_eq] at h1
  obtain ⟨c, hc0, hc1, hc2⟩ := exists_deep (k := k) 1
  obtain ⟨M, hM⟩ := (eventually_mem_twKer (hc := hc0) hc1 hc2 h1).exists
  refine claim_of_antitone hc1 hc2 hπ _ _ rfl (antitone_expo M) v ?_ hM
  exact mem_fixed.2 fun g hg => hfix g ((sup_le KOne_le_KO inf_le_right) hg)

end GlobalTheory.PsType
