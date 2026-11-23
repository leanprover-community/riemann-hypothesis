module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_coef : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (g₁ g₂ : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ) (b₁ b₂ q : R), GlobalTheory.PsiRing.Coef D χ u th g₁ b₁ → GlobalTheory.PsiRing.Coef D χ u th g₂ b₂ → b₁ = q * b₂ → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q g₁ g₂ := by
  intro R _ _ D χ u th g₁ g₂ b₁ b₂ q h₁ h₂ hb
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e : lift (toUnit (𝟙_ _ ⊗ D.P.A)) (snd (𝟙_ _) D.P.A) = 𝟙 _ := by
    rw [toUnit_unique (toUnit _) (fst (𝟙_ _) D.P.A), lift_fst_snd]
  have e₁ := h₁ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  have e₂ := h₂ (𝟙_ _ ⊗ D.P.A) (snd _ _) y J hJ
  rw [e] at e₁ e₂
  refine e₁.trans (Eq.trans ?_ (congrArg (_ * ·) e₂.symm))
  rw [hb, GlobalTheory.IndivisibleSection.cst_mul', _root_.mul_assoc]

end GlobalTheory.PsiRing
