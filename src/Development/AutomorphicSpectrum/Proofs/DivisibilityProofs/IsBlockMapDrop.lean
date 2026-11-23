module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.IsChainFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.FlDeg

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {K : Type}

theorem isBlockMap_drop (j : K → FlBlock Ψ N) (k₀ : K) :
    IsBlockMap (Subtype.val : {k // k ≠ k₀} → K) (dropV j k₀) := by
  refine ⟨Subtype.val_injective, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
    have h' : (⟨a, x⟩ : Σ k, PIdx j k) = ⟨b, y⟩ := h
    cases h'
    rfl
  · rintro ⟨k, x⟩ ⟨⟨k', hk⟩, rfl⟩
    exact ⟨⟨⟨k', hk⟩, x⟩, rfl⟩

theorem imageZ_drop [Fintype K] [DecidableEq K] (j : K → FlBlock Ψ N) (k₀ : K) :
    imageZ (dropV j k₀) (PPart j) = PPart (dropJ j k₀) := by
  have key : ∀ f : MRing (PIdx (dropJ j k₀)), mConeMap (yPart j) (rename (dropV j k₀) f) =
      rename Subtype.val (mConeMap (yPart (dropJ j k₀)) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, yPart, dropV, dropJ]
  ext f
  simp only [imageZ, PPart, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker]
  show mConeMap (yPart j) (rename (dropV j k₀) f) = 0 ↔ _
  rw [key]
  constructor
  · intro h
    exact rename_injective _ Subtype.val_injective (by rw [h, map_zero])
  · intro h
    have h' : mConeMap (yPart (dropJ j k₀)) f = 0 := h
    rw [h', map_zero]

end GlobalTheory.CompanionTheory.Ar.Top.FlDeg
