module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingForm
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

theorem _root_.GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → (∀ a b, x (a + b) = x a * x b) → (∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a) → ∀ t ∈ S.perp l.yy.ker, ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), pk.y = 0 ∧ IsTor τ pk.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk (x t) ∧ ∀ (a : S.Gam) (α : u.D.toPre.X), l.yy a = QuotientAddGroup.mk α → (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ t a).val))) := by
  first | exact @GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | exact GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | (intros; apply GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd <;> assumption)
