module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformiza
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (E : EndU U.toUnifPre) (k' k : ℕ) (β : LB.Gen (LB.LinComb U.LG.L (K := Fin 3) ![𝟙 _, E.aG.left, (1 : G ⟶ G).left] ![(k' : ℤ), -(k : ℤ), (k : ℤ) - k'])), β.IsGen → LB.Gen.Corr U.LG.L _ _ _ _ (LB.pullGen U.LG.L _ _ β (eSec G)) (LB.oneGen U.LG.L) → ∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (x o : Z ⟶ (thickObj R I e G).left) (z : Z) (JG) (J), Good U.LG.L z JG → Good D.toPre.P.L z J → o = x ≫ (1 : thickObj R I e G ⟶ thickObj R I e G).left → ∀ W : (Z ⟶ (thickObj R I e G).left) → (Z.presheaf.stalk z)ˣ, (∀ y, W y = gw (U.w e) y z (J (y ≫ (U.gt e).pG.left)) (fun _ => JG (y ≫ (fstG I e G).left))) → val κ (x ≫ (U.gt e).pG.left) z J = val β (x ≫ (fstG I e G).left) z JG * W x ^ (k' : ℤ) * W (x ≫ ((Over.pullback (thick R I e)).map E.aG).left) ^ (-(k : ℤ)) * W o ^ ((k : ℤ) - k') := by
  first | exact @GlobalTheory.UT.PullDescent.main | exact GlobalTheory.UT.PullDescent.main | (intros; apply GlobalTheory.UT.PullDescent.main <;> assumption)
