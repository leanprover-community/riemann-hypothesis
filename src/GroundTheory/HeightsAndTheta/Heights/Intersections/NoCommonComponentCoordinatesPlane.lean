module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Mathlib.Analysis.InnerProductSpace.Laplacian
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

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsSemiPosHerm (M : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ v : (Σ k, ι k) → ℂ,
    0 ≤ Δ (fun t : ℂ => Real.log (M.h (z + t • v))) 0

def De (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι) : ℝ :=
  ((∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s)) -
    ((∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s'))

theorem De_swap (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (A A' : HermLine ι)
    (s s' : MRing ι) : De P L A' A s' s = -De P L A A' s s' := by
  unfold De
  ring

end Objects

def DeSlotAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (j : Fin n) (M N A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ i, IsSmoothHerm (L i)) → IsSmoothHerm M → IsSmoothHerm N →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P (Function.update L j (M.tensor N)) A A' s s' =
      De P (Function.update L j M) A A' s s' + De P (Function.update L j N) A A' s s'

def SemiPosTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (M : HermLine ι),
    IsSmoothHerm M → ∃ T : HermLine ι, IsSmoothHerm T ∧ IsSemiPosHerm T ∧ IsSemiPosHerm (M.tensor T)

def DeLeSemiPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSemiPosHerm (L j)) →
    IsSmoothHerm A → IsSmoothHerm A' → IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    De P L A A' s s' ≤ 0

end GroundTheory.Heights₂.Heights.Inter
