module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProdUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroups
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

theorem _root_.GlobalTheory.T.uniformisation_product_of_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  first | exact @GlobalTheory.ProdUnifExists.main | exact GlobalTheory.ProdUnifExists.main | (intros; apply GlobalTheory.ProdUnifExists.main <;> assumption)
