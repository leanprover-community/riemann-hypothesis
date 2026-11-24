module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFHoriz
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section


open Classical in
def PFFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (N : Fin (r + 1) → HermLine ι') (s : MRing ι') (a : K' → ℕ),
    IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ k, (N (Fin.last r)).a k = a k) → IsMultiHomog s a → s ∉ P' →
    ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then
          (J (fibreOf κ G W) r (fun j => fibreDeg κ (N (Fin.castSucc j)).a) : ℝ) else 0) =
      (J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) : ℝ)

end

end GroundTheory.Heights₂.Heights.Inter
