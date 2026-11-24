module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastKernelDatumInLastLineFrameAtLevelPrime
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.lastKernelDatum_in_lastLineFrame_at_levelPrime : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∃ (Λ : ι → Submodule 𝒪[k] (Fin c.T.rank → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k) (u : ι → 𝓀[k]ˣ), (∀ i, (o.γ i).IsLat v.NT (Λ i)) ∧ Reps c.ψ (o.β (j + 1)) (o.γ₀ (j + 1 + 1) h) (c.x (j + 1)).L (c.x (j + 1 + 1)).L (fun i => haveI := hΛ i; phiOne (u i • o.Q (j + 1) i) (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.lastPair o.q (Λ i))) o.I (· ∈ v.tP) (v.dT (j + 1)) := by
  exact @GlobalTheory.SeeSaw.lastKernel_reps
