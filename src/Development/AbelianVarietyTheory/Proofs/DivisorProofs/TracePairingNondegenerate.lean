module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem mixedTracePairing_nondegenerate_left {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, trP F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same] at this

theorem mixedTracePairing_nondegenerate_right {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) (hy : ∀ x, trP F κ x y = 0) : y = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hy (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this

theorem mixedTracePairing_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (trP F κ).Nondegenerate := by
  intro F _ _ κ _
  refine ⟨fun x hx => mixedTracePairing_nondegenerate_left (F := F) (κ := κ) x hx, fun y hy => mixedTracePairing_nondegenerate_right (F := F) (κ := κ) y hy⟩

end GlobalTheory.ArchSch
