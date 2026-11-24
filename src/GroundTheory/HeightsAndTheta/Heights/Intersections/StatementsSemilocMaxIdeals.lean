module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocRing
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem semiLocRing_le_locRing (P : Ideal (MRing ι)) {𝒲 : Set (Ideal (MRing ι))} {W : Ideal (MRing ι)}
    (hW : W ∈ 𝒲) : semiLocRing P 𝒲 ≤ locRing P W := by
  unfold semiLocRing locRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, hwW W hW, hu, hwa, rfl⟩

def semiToLoc (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲) :
    semiLocRing P 𝒲 →+* locRing P W :=
  Subring.inclusion (semiLocRing_le_locRing P hW)

theorem semiToLoc_coe (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    (b : semiLocRing P 𝒲) : ((semiToLoc P 𝒲 W hW b : locRing P W) : FractionRing (MRing ι ⧸ P)) = b := by
  simp [semiToLoc]

def semiMaxIdeal (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : Ideal (semiLocRing P 𝒲) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (semiToLoc P 𝒲 W hW)

instance semiMaxIdeal.isPrime (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : (semiMaxIdeal P 𝒲 W hW).IsPrime :=
  Ideal.comap_isPrime _ _

end Objects

def SemilocMaxIdeals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')],
      (semiMaxIdeal P' (fibreOver v P' W) W' hW').IsMaximal ∧
      letI := (semiToLoc P' (fibreOver v P' W) W' hW').toAlgebra
      IsLocalization.AtPrime (locRing P' W') (semiMaxIdeal P' (fibreOver v P' W) W' hW')) ∧
    (∀ (W₁ W₂ : Ideal (MRing ι')) (h₁ : W₁ ∈ fibreOver v P' W) (h₂ : W₂ ∈ fibreOver v P' W)
      [IsLocalRing (locRing P' W₁)] [IsLocalRing (locRing P' W₂)],
      semiMaxIdeal P' (fibreOver v P' W) W₁ h₁ = semiMaxIdeal P' (fibreOver v P' W) W₂ h₂ → W₁ = W₂) ∧
    ∀ M : Ideal (semiLocRing P' (fibreOver v P' W)), M.IsMaximal →
      ∃ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W), ∀ [IsLocalRing (locRing P' W')],
        M = semiMaxIdeal P' (fibreOver v P' W) W' hW'

end GroundTheory.Heights₂.Heights.Inter
