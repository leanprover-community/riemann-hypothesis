module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem jetInVV_of_stepWeights : ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (a b : ℕ), a < b → ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b), (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.StepWeights (lam τ) (nu τ) (lam' τ)) → JetInVV K lam lam' fun τ => GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry (nu τ) := by
  intro K _ _ ι _ a b hlt lam ν lam' hw J P hP
  choose s' hs' using fun τ => (hw τ).2.1
  choose s hs using fun τ => (hw τ).2.2
  refine GlobalTheory.JetPoint.jetMap_mem hlt.le _ _ _ (fun ap => ?_) J
  refine GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hlt lam lam' s (fun τ => if 0 < a then s' τ else 0) _
    ⟨fun τ i => ?_, fun τ j hj => ?_, fun τ => ?_⟩ ap _ hP
  · have h := hs τ (Fin.castLE hlt.le i)
    have h0 := hs' τ i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero, Fin.val_castLE, i.2, dif_pos, Fin.eta] at h
    simp only [Fin.pos i, if_true]
    omega
  · have h := hs τ j
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.padZero, dif_neg (not_lt.2 hj)] at h
    omega
  · unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.lastEntry DomWeight.detShift
    split_ifs with h
    · have h0 := hs' τ ⟨a - 1, by omega⟩
      have h1 := (hw τ).1 ⟨a - 1, by omega⟩
      simp only
      omega
    · simp

end GlobalTheory.ColNorms
