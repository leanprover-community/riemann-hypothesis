module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagPivot
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.HasCoverByOne
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

abbrev GenFrac (F : Type) [Field F] (Ψ : Type) (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Ψ × Fin n × Fin n) F)

def genMatFr (F : Type) [Field F] (Ψ : Type) (n : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b =>
    algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n) (X (τ, a, b))

def flagMinorRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : Ψ × Σ j : Fin (n - 1), PluckerBlocks n n j) :
    GenFrac F Ψ n :=
  flagMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2 / leadMinor (genMatFr F Ψ n q.1) q.2.1

abbrev PivotIdx (Ψ : Type) (n : ℕ) : Type := Ψ × Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) < b}

def pivotRatio (F : Type) [Field F] (Ψ : Type) (n : ℕ) (q : PivotIdx Ψ n) : GenFrac F Ψ n :=
  pivotMinor (genMatFr F Ψ n q.1) q.2.1 q.2.2.1 / leadMinor (genMatFr F Ψ n q.1) q.2.1

theorem PlueckerData.ofΩ_eq {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type}
    [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D)
    (x : Ω) : Pl.ofΩ x = algebraMap Ω (GenFrac Ω Ψ D.N) x := by
  rw [PlueckerData.ofΩ, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply Ω (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) (GenFrac Ω Ψ D.N)]

end GroundTheory.Heights₂.Heights.LowerBoundFree
