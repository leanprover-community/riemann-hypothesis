module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaValueEqRootMulThetaOperatorValue
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum


theorem _root_.GlobalTheory.T.twistedThetaValue_eq_root_mul_thetaOperatorValue : ∀ {o Ω o' Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] [CommRing o'] [Field Ω'] [Algebra o' Ω'] [ArithBase o' Ω'] {S : ThetaSys o Ω} {S' : ThetaSys o' Ω'} (ρ : S.Real) (ρ' : S'.Real) (lab : S.Gam → S'.Gam) (φ : Ω →+* Ω') (P₀ : PolAV (Sp Ω')) (a : P₀.A.left ⟶ ρ.P.A.left) (a' : P₀.A.left ⟶ ρ'.P.A.left) (x : S'.Gam → (genPt (φ.comp S.R.val.toRingHom) ⟶ ρ.P.A)), IsGenLab ρ ρ' lab φ P₀ a a' x → ∀ (m : ℕ), S'.N = m ^ 2 → ∀ (κ x₀ : S.Gam) (h : S'.Gam), m • h = lab κ → ∃ ξ : Ω', (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ (t : S'.Gam) (v : Ω'), IsTwVal ρ.P S'.N m ρ.th₁ (ρ.fr κ) (genTo _) (x (S'.r • t)) (x h) ((Scheme.ΓSpecIso (CommRingCat.of Ω')).inv.hom v) → v * S'.th (lab x₀) = ξ * φ (S.th x₀) * ∑ j, algebraMap o' Ω' (S'.ρ t j ρ'.i₀) * S'.ev h j := by
  first | exact @GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | exact GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul | (intros; apply GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul <;> assumption)
