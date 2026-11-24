module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibAc
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FibreAcyclicityOfSections
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.fibre_acyclicity_of_sections : ∀ {k : Type} [Field k] [IsAlgClosed k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) (ha : IsProjBy a) [IsProper a] [Flat a] [IsProper b] (G : LB Z) (hG : G.IsLB)
    (hfib : ∀ (y : Sp k ⟶ T) (σ : X ⟶ Z), y ≫ b = 𝟙 _ → σ ≫ p = 𝟙 X → σ ≫ q = a ≫ y → FibAc a (G.pull σ)), FibAc (p ≫ a) G := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | exact GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres | (intros; apply GlobalTheory.CompanionTheory.PointSurjTotal.fibAc_comp_of_fibres <;> assumption)
