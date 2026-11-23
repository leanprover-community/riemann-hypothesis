module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenericMinors
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

def genMat0Fr (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) : Matrix (Fin n) (Fin n) (GenFrac F Ψ n) :=
  Matrix.of fun a b => if (a : ℕ) < j ∧ j ≤ (b : ℕ) then 0 else genMatFr F Ψ n τ a b

def flagMinorRatio0 (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (q : Ψ × Σ i : Fin (n - 1), PluckerBlocks n n i) :
    GenFrac F Ψ n :=
  flagMinor (genMat0Fr F Ψ n j q.1) q.2.1 q.2.2 / leadMinor (genMat0Fr F Ψ n j q.1) q.2.1

def HodgeFlagMinorTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ψ : Type) [Fintype Ψ] (n j : ℕ), j ≤ n →
    Algebra.trdeg F (IntermediateField.adjoin F (Set.range (flagMinorRatio0 F Ψ n j))) =
      ((Fintype.card Ψ * (j * (j - 1) / 2 + (n - j) * (n - j - 1) / 2) : ℕ) : Cardinal)

end GroundTheory.Heights₂.Heights.LowerBoundFree
