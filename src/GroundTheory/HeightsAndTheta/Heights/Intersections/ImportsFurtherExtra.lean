module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.PullBad
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M

open ReciprocityTheory.ChartRestriction.G in
def pullbackDensity_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ)
    (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (L : Fin n → Geo.HermLine ι) (L' : Fin n → Geo.HermLine ι')
    (A : Geo.HermLine ι) (A' : Geo.HermLine ι') (s : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsGoodProj (imageZ v P') Ψ →
    (∀ j, Geo.IsSmoothHerm (L j)) → (∀ j, AI.I4.IsPullHerm κ v (L j) (L' j)) →
    Geo.IsSmoothHerm A → AI.I4.IsPullHerm κ v A A' → Geo.IsSectionOn (imageZ v P') A s →
    ∀ᵐ y : Fin n → ℂ, ∀ x ∈ pullQ R v Ψ ⁻¹' {y} \ pullBad R v Ψ,
      Geo.logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => Geo.potOf R (L' j)) (pullQ R v Ψ) x =
        sheetDensity (imageZ v P') Ψ (Geo.pot L) (Geo.logNorm A s) y (pullW R v Ψ x)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
