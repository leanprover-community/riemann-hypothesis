module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices.InstFintypeFlIdx
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

structure IsChain (j : K → FlBlock Ψ N) : Prop where
  inj : Function.Injective j
  down : ∀ k (q : FlBlock Ψ N), q.1 = (j k).1 → (q.2 : ℕ) ≤ (j k).2 → q ∈ Set.range j

abbrev PIdx (j : K → FlBlock Ψ N) : K → Type := fun k => FlIdx Ψ N (j k)

def yPart (j : K → FlBlock Ψ N) : (Σ k, PIdx j k) → ΩFl Ψ N := fun p => yFl Ψ N ⟨j p.1, p.2⟩

def PPart [Fintype K] (j : K → FlBlock Ψ N) : Ideal (MRing (PIdx j)) := mCoordIdeal (yPart j)

def unitLine [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k : K) : HermLine (PIdx j) :=
  fsHerm (PIdx j) fun k' => if k' = k then 1 else 0

def cellDim [Fintype K] (j : K → FlBlock Ψ N) : ℕ := ∑ k, (N - 1 - ((j k).2 : ℕ))

def dropJ (j : K → FlBlock Ψ N) (k₀ : K) : {k // k ≠ k₀} → FlBlock Ψ N := fun k => j k.1

def dropV (j : K → FlBlock Ψ N) (k₀ : K) : (Σ k, PIdx (dropJ j k₀) k) → Σ k, PIdx j k := fun p => ⟨p.1.1, p.2⟩

def constLine {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofWeight (fun _ => -1) fun _ _ _ => rfl

def rhoM (Ψ : Type) [Fintype Ψ] (N : ℕ) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => N - 1 - (p.2 : ℕ)

def gapDelta (Ψ : Type) [Fintype Ψ] (N : ℕ) : MvPolynomial (Ψ × Fin N) ℝ :=
  ∏ τ : Ψ, ∏ a : Fin N, ∏ b ∈ Finset.Ioi a, ∑ s ∈ Finset.Ico a b, X (τ, s)

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
