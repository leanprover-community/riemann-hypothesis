module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidifiedBundleTwoPullbacksCompare
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
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

theorem _root_.GlobalTheory.T.rigidified_bundle_two_pullbacks_compare : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (ρ₀ : LB.Gen (L₀.pull (eSec G₀))), ∀ (S S' : Scheme.{0}) (x : S ⟶ Z) (f : S' ⟶ S) (G : Over S) [GrpObj G] (G' : Over S') [GrpObj G'] (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → ∀ (φ : G.left ⟶ G₀.left) (φ' : G'.left ⟶ G₀.left) (w : LB.Iso L (L₀.pull φ)) (w' : LB.Iso L' (L₀.pull φ')) ρ ρ', RigPull G G₀ x φ w ρ ρ₀ → RigPull G' G₀ (f ≫ x) φ' w' ρ' ρ₀ → ∃ (ψ : G'.left ⟶ G.left) (ω : LB.Iso L' (L.pull ψ)), RigPull G' G f ψ ω ρ' ρ ∧ ∀ (k : ℕ) (T₀ : Over Z) (T : Over S) (T' : Over S') (p : T.left ⟶ T₀.left) (q : T'.left ⟶ T.left), p ≫ T₀.hom = T.hom ≫ x → q ≫ T.hom = T'.hom ≫ f → ∀ s₀ s s', Thru w k (T' := T) (T := T₀) p s₀ s → Thru w' k (T' := T') (T := T₀) (q ≫ p) s₀ s' → Thru ω k (T' := T') (T := T) q s s' := by
  first | exact @GlobalTheory.OneBasis.Compare.rigPull_compare | exact GlobalTheory.OneBasis.Compare.rigPull_compare | (intros; apply GlobalTheory.OneBasis.Compare.rigPull_compare <;> assumption)
