module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.GenericFibrePoint

theorem fibre_map_univ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y yF x φ hgp hL
  have hsq : φ ≫ Y.t.G.hom = (x.P.A.hom ≫ yF) ≫ (Y.jQ ≫ pullback.fst _ _) := by
    rw [hgp.1.w, Category.assoc]; rfl
  let φ' : x.P.A.left ⟶ Y.oF.t.G.left := Y.m.cart.1.lift φ (x.P.A.hom ≫ yF) hsq
  have h1 : φ' ≫ Y.m.φ = φ := Y.m.cart.1.lift_fst _ _ _
  have h2 : φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF := Y.m.cart.1.lift_snd _ _ _
  have hn : IsGrpPullback x.P.A Y.t.G (yF ≫ (Y.jQ ≫ pullback.fst _ _)) (φ' ≫ Y.m.φ) := by
    rw [h1]; exact hgp
  have hc : IsGrpPullback x.P.A Y.oF.t.G yF φ' := IsGrpPullback.cancel Y.m.cart hn h2
  refine ⟨φ', h1, h2, hc.comp Y.m0.toSABMap.cart, ?_⟩
  obtain ⟨w, hw, -⟩ := Y.m.lin
  obtain ⟨w0, hw0, -⟩ := Y.m0.toSABMap.lin
  have k : LBIso (Y.t.PP.L.pull Y.m.φ) (Xo.univ.t.PP.L.pull Y.m0.toSABMap.φ) :=
    LBIso.trans (pull_isLB Y.t.PP.isLB _) Y.oF.t.PP.isLB (pull_isLB Xo.univ.t.PP.isLB _)
      (LBIso.symm ⟨w, hw⟩) ⟨w0, hw0⟩
  have k' : LBIso (Y.t.PP.L.pull φ) (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) :=
    GlobalTheory.Spread.lbIso_pull_comp φ' h1.symm rfl k
  exact LBIso.trans x.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL k'

end GlobalTheory.GenericFibrePoint
