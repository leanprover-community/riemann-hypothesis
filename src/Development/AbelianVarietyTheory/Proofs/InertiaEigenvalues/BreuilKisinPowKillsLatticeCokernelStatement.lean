module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_pow_kills_lattice_cokernel : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (N : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H → (∀ τ, D₁.desc.chars τ ⊆ (Sig : Set (ZMod e))) → (∀ τ, D₂.desc.chars τ ⊆ (Sig : Set (ZMod e))) → IsFiniteLength (A O K) F.coker → GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.KillsCoker F.app (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N) D₁.L D₂.L := by
  first | exact @GlobalTheory.CokerL.kills_cokerL | exact GlobalTheory.CokerL.kills_cokerL | (intros; apply GlobalTheory.CokerL.kills_cokerL <;> assumption)
