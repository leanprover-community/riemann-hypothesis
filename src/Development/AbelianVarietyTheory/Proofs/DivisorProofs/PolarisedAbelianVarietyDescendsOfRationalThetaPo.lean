module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomOfFiniteTypeOfIsAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureRationalThetaPointSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadPolarisedAbelianVarietyFinitelyManyPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadModelFibreAtPointIsGivenVarietyStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ThetaDescent

theorem descends : ∀ (F Ω : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (n : ℕ), n.Prime → Odd n → (∀ j : ℕ, 1 ≤ j → ∃ (Ix : Type) (x : Ix → (baseOver (Sp Ω) ⟶ A.A)) (v : Ix → F), (∀ z : baseOver (Sp Ω) ⟶ A.A, z ^ ((n ^ j) ^ 2) = 1 → ∃ i, x i = z) ∧ IsThetaPt A (n ^ j) x fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → ∃ (A₀ : PolAV (Sp F)) (a : A.A.left ⟶ A₀.A.left), IsGrpPullback A.A A₀.A (spMap em) a ∧ LBIso A.L (A₀.L.pull a) := by
  intro F Ω _ _ _ _ _ em A n hn ho hyp
  set J := ((n ^ 2) ^ 2) ^ A.g * A.g.factorial + 4 with hJ
  have hJ4 : 4 ≤ J := by omega
  have hb : ((n ^ 2) ^ 2) ^ A.g * A.g.factorial < n ^ J :=
    lt_of_lt_of_le (by omega) (Nat.lt_pow_self hn.one_lt).le
  obtain ⟨Ix, x, v, hcov, hth⟩ := hyp J (by omega)
  obtain ⟨ζ, lev, v', hζ, hv'⟩ := GlobalTheory.T.exists_level_structure_rational_thetaPoint_subfield F Ω em A n J hn (by omega) Ix x v hcov hth
  obtain ⟨T, _, _, _, jT, P, φ, y₀, hft, hinj, hcomp, hP, hL, hy⟩ :=
    GlobalTheory.T.exists_spread_polarisedAbelianVariety_finitely_many_points F Ω em A (Fin (2 * A.g)) lev.pt
  obtain ⟨t⟩ := GlobalTheory.exists_algHom_of_finiteType_of_isAlgClosed F T F
  exact GlobalTheory.T.spreadModel_fibre_at_point_isGivenVariety F Ω T em jT t hft hinj hcomp A P φ hP hL n J hn ho hJ4 hb ζ lev y₀ v' hζ hy hv'

end GlobalTheory.ThetaDescent
