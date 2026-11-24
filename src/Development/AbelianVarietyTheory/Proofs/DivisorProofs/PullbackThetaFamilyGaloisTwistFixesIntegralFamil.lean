module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem famTw_eq_of_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  intro R _ _ I D N σ F₀ s hs
  have hL := D.P.isLB
  refine fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (sec_ext' hL fun y J hJ => ?_)
  show sval (termPull D (Kb R) (TwF σ) N α (s.s α)) (𝟙 _) y J = _
  refine (sval_pullOver _ _ _ _ hJ).trans ?_
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, ← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ]
  congr 1
  have e : (famMap D (Kb R) (TwF σ)).left ≫ (DegPre.prB D (Kb R)).left = (DegPre.prB D (TwF σ)).left :=
    congrArg (fun q => q.left) (famMap_snd D (Kb R) (TwF σ))
  exact (Category.assoc _ _ _).trans (congrArg (fun q => 𝟙 _ ≫ q) e)

end GlobalTheory.Mum.Conj
