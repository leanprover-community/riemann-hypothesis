module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.NullExp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → NullFam I f := by
  intro R _ _ I D A G _ _ U T k σ f H e
  obtain ⟨s, hs⟩ := H e
  refine ⟨s, fun α hα Z r hr z J hJ => ?_⟩
  refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (f α)
    ?_ Z r hr z J hJ
  intro Z x r hx z J hJ
  have hc : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, Over.w (fst T D.P.A), Over.w (fstG I e G), ← Over.w (snd T D.P.A),
      ← Category.assoc, hx, Category.assoc, Over.w (U.gt e).pG]
  let rG : Z ⟶ (T ⊗ G).left := pullback.lift (r ≫ (fst T D.P.A).left) (x ≫ (fstG I e G).left) hc
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  exact (hs Z x rG r (pullback.lift_snd _ _ _) hx (pullback.lift_fst _ _ _).symm z JG J hJG hJ).1 α hα

end GlobalTheory.NullExp
