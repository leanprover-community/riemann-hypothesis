module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights


theorem _root_.GlobalTheory.T.exists_graded_sandwich_coordinates : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (p : Cpt ξ) (c : (k : K) → J k), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p →
    ∃ (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (κ : Ω), (∀ n : ℕ, flagStep Ω b n = flagStep Ω b₀ n) ∧
      V.IsFrameAt b p ∧ (∀ j, (m : Ω) • b j ∈ M.lat p) ∧ (∀ j l, π j (b l) = if j = l then 1 else 0) ∧
      (∀ j, ∀ e ∈ M.lat p, (m : Ω) * π j e ∈ regAt ξ p) ∧ κ ≠ 0 ∧ κ ∈ regAt ξ p ∧ κ⁻¹ ∈ regAt ξ p ∧
      ∀ (e : Li) (t : Ω), e ∈ flagStep Ω b₀ (i + 1) → IsCls b₀ i e t → t / gen y a e₀ c = π i e * κ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame | exact GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.cls_frame <;> assumption)
