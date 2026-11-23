module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianDescentAlongProperSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsNearClosedFibreStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G)
    (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧
    IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG' N hL
  have hNoeth : IsNoetherianRing R := hA.1
  have hIC : IsIntegrallyClosed R := hA.2.2.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_descentDatum_of_descendedMultiplication R hA S π hP hS hI G' hG' N hL
  obtain ⟨G, β, i, hsm, hpb, hop, hu, hc⟩ := GlobalTheory.T.semiAbelian_descends_near_closedFibre R hA S π hP hS hI G' hG' N hL φ hφ
  obtain ⟨g, c, hsa, hgp⟩ := GlobalTheory.T.exists_semiAbelian_descent_along_proper_surjective R S π hP hS hI G' hG' G β hsm hpb φ hφ.1 hc
  exact ⟨G, g, c, β, i, hsa, hgp, hop, hu⟩

end GlobalTheory.Mum
