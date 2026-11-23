module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcR
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationDifferenceTrivialBaseChangeIffOverA
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.translationDifference_trivial_baseChange_iff_over_A : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V] (φ : Sp V ⟶ T.left) (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), N.IsLB → ∀ (Y : Over (Sp V)) (x : Y ⟶ GlobalTheory.TwistFlat.bc A φ) (U : Y.left.Opens), Triv ((LB.div (translDiff (GlobalTheory.TwistFlat.bc A φ) (L.pull (pullback.fst A.hom (φ ≫ T.hom))) x) ((GlobalTheory.TwistFlat.twist A φ N).pull (snd Y (GlobalTheory.TwistFlat.bc A φ)).left)).pull ((fst Y (GlobalTheory.TwistFlat.bc A φ)).left ⁻¹ᵁ U).ι) ↔ Triv ((LB.div (translDiff A L (GlobalTheory.TwistFlat.upa φ x)) (ev N (snd (GlobalTheory.TwistFlat.up φ Y) A) (fst (GlobalTheory.TwistFlat.up φ Y) A ≫ GlobalTheory.TwistFlat.upt φ Y))).pull ((fst (GlobalTheory.TwistFlat.up φ Y) A).left ⁻¹ᵁ U).ι) := by
  exact @GlobalTheory.TwistFlat.triv_twist_iff
