module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniformizationEndomorphismOfLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommuteStatement
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT.OLinTors

theorem main : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (k : ℕ), 1 ≤ k → ∀ f, Tors U.toUnifPre F k f → ∀ a p p', QkAct ιD a p p' → f p' = f p ≫ ιA.act a := by
  intro hL h₁ h₂ h₃ h₄ R _ _ _ I hI D A G _ _ hG U F _ _ _ O _ _ _ ιD ιA ιG hlin hcube k hk f hf a p p' hp
  obtain ⟨E, eG, eA, -, -, eact⟩ := GlobalTheory.UT.OLinEnd.main hL R I hI D A G hG U O ιD ιA ιG hlin a
  obtain ⟨E', eG', -, -, eh', -⟩ := GlobalTheory.UT.OLinEnd.main hL R I hI D A G hG U O ιD ιA ιG hlin (star a)
  obtain ⟨q, hy, hg, hq⟩ := hp
  have hb := (GlobalTheory.T.uniformisation_adjoint_endomorphisms_commute hL h₁ h₂ h₃ h₄ R I hI D A G hG U F E E' (by rw [eG, eG']; exact hcube a)).2 k hk p q (f p)
    (by rw [eh', star_star]; exact hy) ((eact F _ _).2 hg) ((hf.1 p _).2 rfl)
  have e := (hf.1 q _).1 hb
  rw [eA] at e
  rw [e]
  first | exact (hf.2.2.1 _ _).2 hq | exact ((hf.2.2.1 _ _).2 hq).symm
end GlobalTheory.UT.OLinTors
