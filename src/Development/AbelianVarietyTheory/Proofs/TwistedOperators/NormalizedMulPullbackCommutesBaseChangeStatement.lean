module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChange
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.normalized_mul_pullback_commutes_base_change : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  first | exact @GlobalTheory.HeckeExBC.isMulPull_baseChange | exact GlobalTheory.HeckeExBC.isMulPull_baseChange | (intros; apply GlobalTheory.HeckeExBC.isMulPull_baseChange <;> assumption)
