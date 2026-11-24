module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImage
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def BlockImageInverse.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (k₀ : K) (r : ℕ) (M : Matrix (Ix (Fin r)) (ι k₀) ℤ)
    (N : Matrix (ι k₀) (Ix (Fin r)) ℤ) (x : Ix (Fin r) → Ω) (J : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → BlockBirational y k₀ → IsBlockImage y k₀ M N x →
      LinearIndependent ℤ x → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y →
      ∃ (F : MvPolynomial (Ix (Fin r)) ℤ) (e : ℕ) (G : MRing ι) (dG : K → ℕ),
        IsMultiHomog (ι := GlobalTheory (Fin r)) F (fun _ => e) ∧ F ∉ coordIdeal ℤ x ∧
        IsMultiHomog G dG ∧ G ∉ mCoordIdeal y ∧
        (∀ z, eval z (map (Int.castRingHom ℂ) G) = eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F)) ∧
        (∀ u ∈ mcPts (ι := GlobalTheory (Fin r)) (coordIdeal ℤ x), eval u (map (Int.castRingHom ℂ) F) ≠ 0 →
          ∃ z ∈ mcPts (mCoordIdeal y), z ∉ mcPts J ∧ SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) u) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 → z ∉ mcPts J) ∧
        (∀ z ∈ mcPts (mCoordIdeal y), ∀ z' ∈ mcPts (mCoordIdeal y),
          eval (blockMapC k₀ M z) (map (Int.castRingHom ℂ) F) ≠ 0 →
          SameOrbit (ι := GlobalTheory (Fin r)) (blockMapC k₀ M z) (blockMapC k₀ M z') → SameOrbit z z')

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
