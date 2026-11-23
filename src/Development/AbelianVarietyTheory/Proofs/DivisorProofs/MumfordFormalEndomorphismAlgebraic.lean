module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreHomOfFormalSectionRatiosStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordThickeningEndomorphismMapsSectionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheriaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatiosStatement
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem formalEnd_algebraic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ g : G ⟶ G, IsMonHom g ∧ ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hR D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, S, hS, hnd⟩ := GlobalTheory.T.mumford_thickening_endomorphism_maps_sections R hR D A G hG U a a' h h' hE b hb
  obtain ⟨φ, hφ, hgen⟩ := GlobalTheory.T.exists_genericFibreHom_of_formalSectionRatios R hR D A G hG U a a' h h' hE b hb N S hN hS hnd
  have := hR.1.1
  have := hR.1.2.2.1
  obtain ⟨g, hg, hgφ⟩ := GlobalTheory.T.semiAbelian_genericFibre_hom_extends_normal_noetherian R G hG φ hφ
  exact ⟨g, hg, GlobalTheory.T.thickening_eq_of_generic_section_ratios R hR D A G hG U a a' h h' hE b hb N S hS hnd φ hgen g hg hgφ⟩

end GlobalTheory.Mum
