module

public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel Filter Topology
open GlobalTheory.LocMod GlobalTheory.LocMod.Witness
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatFBCompare

section Val

variable {K L : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

theorem val_lt_one_iff (x : K) : valuation K x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  refine ⟨GlobalTheory.LocalTraceSum.tendsto_pow, fun h => ?_⟩
  have hO := GlobalTheory.LocalTraceSum.isOpen_lt (K := K) 1
  obtain ⟨n, hn⟩ := (h.eventually (hO.mem_nhds (by simp))).exists
  by_contra hx
  have h2 : 1 ≤ valuation K (x ^ n) := by rw [map_pow]; exact one_le_pow₀ (not_lt.1 hx)
  exact absurd hn (not_lt.2 h2)

end Val

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  [Fintype Z'] [DecidableEq Z'] {S T : HSp D}

section Scal

variable {K : Type} [Field K] {γ t : Kˣ} {s : K} {σ : ℕ}

end Scal

section Frames

variable {q : GlobalTheory.FinPl.SplitPt D k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {σ : ℕ}
  {γ t : kˣ} {s : k} (hγ : (γ : k) = (Place.ofSplitPt q).xi) (ht : (t : k) = s * γ ^ (σ + 1))
include hγ ht

end Frames

section Local

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

variable [MeasurableSpace k] [BorelSpace k] {c : ℕ}

end Local

section Change

variable {q : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {σ : ℕ} {γ γ' t : kˣ}

end Change

section Rename₂

variable {n m A B : Type} [Fintype n] [DecidableEq n] [Unique A] [Unique B] (a : k)

end Rename₂

end GlobalTheory.FlatFBCompare
end
