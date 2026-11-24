module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpFOfFam
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfMatchStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FiniteExponentBaseChangeFieldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FunctionalEquationAllDegreesAlgebraicClosureStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmResPull
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

namespace GlobalTheory.UU

theorem exists_unif_of_fe_one : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G), U.FE (Kbar V) 1 → ∃ U' : Unif (IsLocalRing.maximalIdeal V) D A G, Match U U'.toUnifPre := by
  intro hL hL2 V _ _ _ hV D A G _ _ U h1
  obtain ⟨U', hM⟩ := ToChart.exists_match V (IsLocalRing.maximalIdeal V) D A G U
  refine ⟨⟨U', fun k hk => ?_⟩, hM⟩
  have hb : U.FE (Kbar V) k := GlobalTheory.T.functional_equation_all_degrees_algebraic_closure hL hL2 V hV D.toPre A G U D.tau_bimult h1 k hk
  have hF : U.FE (FractionRing V) k :=
    GlobalTheory.T.finite_exponent_base_change_field hL.globalFns V hV D.toPre A G U k hb (FractionRing V)
  exact GlobalTheory.T.expBij_of_match_of_fam_expF hL hL2 V hV D A G U U' hM k hk hF
    (ExpOnto.exists_expF_of_fam hL hL2 V hV D.toPre A G U D.tau_bimult (FractionRing V) k hk hF)

end GlobalTheory.UU
