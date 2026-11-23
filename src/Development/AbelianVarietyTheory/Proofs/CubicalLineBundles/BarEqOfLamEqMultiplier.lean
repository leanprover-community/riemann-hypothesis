module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLamEqStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LbIsoCubeLBMulRightOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RingOfIntegersActionInjectiveOnAbelianSchemeStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem bar_eq_of_lamEq_multiplier : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (P B : Out.PolAV (Sp (𝓞 K))) (act : OAct (𝓞 E) P.A) (f : P.A ⟶ B.A) (h : 𝓞 E), 1 ≤ P.g → (∀ a, LamEq P.L (act.act a) (𝟙 P.A) P.L (𝟙 P.A) (act.act (H.bar a))) → LamEq B.L f f P.L (act.act h) (𝟙 P.A) → H.bar h = h := by
  intro hL E _ _ _ H K _ _ P B act f h hg hadj hf
  have : IsLocallyNoetherian (Sp (𝓞 K)) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (𝓞 K))))
  have : IsCommMonObj P.A := P.isAb.comm
  have : IsCommMonObj B.A := B.isAb.comm
  have c := GlobalTheory.LamCalc.lamEq_calculus (Sp (𝓞 K)) P.A P.A

  have h₁ : LamEq B.L f f P.L (𝟙 P.A) (act.act h) :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 hf).2.1
  have h₂ : LamEq P.L (𝟙 P.A) (act.act h) B.L f f :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 h₁).1
  have h₃ : LamEq B.L f f P.L (𝟙 P.A) (act.act (H.bar h)) :=
    ((c B.A P.A P.A B.L P.L P.L B.isLB P.isLB P.isLB f f f f _ (𝟙 _) _ (𝟙 _) _ _).2.1 hf).2.2.1 (hadj h)
  have h₄ : LamEq P.L (𝟙 P.A) (act.act h) P.L (𝟙 P.A) (act.act (H.bar h)) :=
    ((c P.A B.A P.A P.L B.L P.L P.isLB B.isLB P.isLB _ (𝟙 _) _ (𝟙 _) f f f f _ _).2.1 h₂).2.2.1 h₃
  have h₅ : LamEq P.L (act.act h) (𝟙 P.A) P.L (act.act (H.bar h)) (𝟙 P.A) :=
    ((c P.A P.A P.A P.L P.L P.L P.isLB P.isLB P.isLB _ (𝟙 _) _ (𝟙 _) _ (𝟙 _) _ (𝟙 _) (𝟙 _) (𝟙 _)).2.1 h₄).2.1
  exact (GlobalTheory.T.ringOfIntegersAction_injective_on_abelianScheme hL E K P act hg (GlobalTheory.T.eq_of_lamEq_polAV hL _ P _ _ _ h₅)).symm

end GlobalTheory.LamF
