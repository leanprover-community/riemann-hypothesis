module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExponentInertiaTateModuleFiniteResidueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteImageTateModuleOfBoundedExponentCommStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfNeronOggShafarevich
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplicaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionUnramifiedImpTateModuleAndInfinite
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
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.ExistsLinearIndependentNormLe

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit

theorem cmPotentialGoodReduction_of_nos (hN : GlobalTheory.Published.NeronOggShafarevichSt) :
    GlobalTheory.Published.CMPotentialGoodReductionSt := by
  intro R K _ _ _ _ _ _ _ A _ hA F _ _ hF
  have : IsCommMonObj A := hA.comm
  obtain ⟨V, hV⟩ := exists_isAbove R K (SeparableClosure K)
  obtain ⟨l, hl, hlk⟩ := GlobalTheory.Proof.exists_prime_natCast_ne_zero (ResidueField R)
  have hlK : (l : K) ≠ 0 := by
    intro h
    apply hlk
    have h1 : (l : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h])
    rw [← map_natCast (residue R), h1, map_zero]
  have hc := GlobalTheory.T.tateModule_galoisImages_commute_of_complexMultiplication K (SeparableClosure K) A hA F hF l hlK
  have he := GlobalTheory.T.exists_exponent_inertia_tateModule_finite_residue R K (SeparableClosure K) V hV A hA l hlk hc
  obtain ⟨⟨d, hd, -⟩, -⟩ := hF
  have hcard := GlobalTheory.T.card_abelianVariety_torsion_sepClosed K (SeparableClosure K) A hA d hd (l ^ 2)
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlK)
  have hfin : Finite {x : ptOver K (SeparableClosure K) ⟶ A // x ^ (l ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (pow_ne_zero _ hl.out.ne_zero))
  exact (GlobalTheory.potentialGoodReduction_of_neronOggShafarevich hN R K (SeparableClosure K) V hV A hA l hlk).2
    (GlobalTheory.T.finite_image_tateModule_of_bounded_exponent_comm K (SeparableClosure K) A l _ hfin hc he)

end UpperTheory.Lit
