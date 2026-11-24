module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericFibreGroupFactorsUniversalCartesian
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries


theorem _root_.GlobalTheory.T.genericFibre_group_factors_universal_cartesian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (yF : Sp ℂ ⟶ Xo.XF c) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), IsGrpPullback x.P.A Y.t.G (yF ≫ Y.j) φ → LBIso x.P.L (Y.t.PP.L.pull φ) → ∃ φ' : x.P.A.left ⟶ Y.oF.t.G.left, φ' ≫ Y.m.φ = φ ∧ φ' ≫ Y.oF.t.G.hom = x.P.A.hom ≫ yF ∧ IsGrpPullback x.P.A Xo.univ.t.G (yF ≫ pullback.fst _ _) (φ' ≫ Y.m0.toSABMap.φ) ∧ LBIso x.P.L (Xo.univ.t.PP.L.pull (φ' ≫ Y.m0.toSABMap.φ)) := by
  first | exact @GlobalTheory.GenericFibrePoint.fibre_map_univ | exact GlobalTheory.GenericFibrePoint.fibre_map_univ | (intros; apply GlobalTheory.GenericFibrePoint.fibre_map_univ <;> assumption)
