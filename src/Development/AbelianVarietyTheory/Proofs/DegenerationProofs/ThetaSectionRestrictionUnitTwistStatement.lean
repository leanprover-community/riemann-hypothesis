module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSectionRestrictionUnitTwist
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.theta_section_restriction_unit_twist : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N N' : M.Z.Opens) (σ : Q.SecFam N) (c f : Ω), N' ≤ N → (∀ z ∈ N', f ≠ 0 ∧ f ∈ M.O z ∧ f⁻¹ ∈ M.O z) → σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → Q.ThMul c N σ → Q.FibNe N σ → ∃ σ' : Q.SecFam N', σ' ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N') ∧ Q.ThMul (f * c) N' σ' ∧ Q.FibNe N' σ' := by
  first | exact @GlobalTheory.ZH.ZHPre.exists_scale_section | exact GlobalTheory.ZH.ZHPre.exists_scale_section | (intros; apply GlobalTheory.ZH.ZHPre.exists_scale_section <;> assumption)
