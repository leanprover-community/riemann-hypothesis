module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.VolumeFlatSection
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableSetPreSingleton
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GLVolumeIndex
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

namespace GlobalTheory.ChainStepIdentities

theorem volAdd_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (r : ℕ) :
    volAdd ν r = ∏ i ∈ Finset.Icc 1 r, (zetaAt (resCard k) i)⁻¹ := by
  have := hν.1
  have h := GlobalTheory.IndexVolume.volumeOfGL ν hν.2 (Fin r)
  have hS : (Units.val '' (KO k (Fin r) : Set (GL (Fin r) k)) : Set (Matrix (Fin r) (Fin r) k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.groupSet (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, trivial, rfl⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, rfl⟩
  have e : volAdd ν r = GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup ν (⊤ : Subgroup (GL (Fin r) 𝒪[k])) := by
    unfold volAdd GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.volGroup
    rw [hS]
    rfl
  rw [e, h, Fintype.card_fin, Formalism.MainNotions.ZetaProductPairs.qE]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [zetaAt, GlobalTheory.IndefiniteRowSideFullHecke.GLVolumeIndex.resCard, resCard, _root_.zpow_neg, _root_.zpow_natCast]

end GlobalTheory.ChainStepIdentities
