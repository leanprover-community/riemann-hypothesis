module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOneOfFiniteOrderAny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PtEqOfProportional
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section

namespace GlobalTheory.DvrAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
section
open GlobalTheory.UT.CoefUnit GlobalTheory.UT.CoefBasic

end
section
open GlobalTheory.UT.SmallPoint GlobalTheory.UT.CoefBasic

end
section
open GlobalTheory.UT.SmallZero GlobalTheory.UT.CoefBasic GlobalTheory.UT.SmallPoint

end
end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar
open GlobalTheory.TorsionAnyChar GlobalTheory.UT.MixedConv GlobalTheory.FieldBaseChange
section CoreAny
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]

end CoreAny
section FieldAny
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G} (E : EndU U)
  {F : Type} [Field F] [Algebra (FractionRing R) F]

end FieldAny

end GlobalTheory.DvrAnyChar

namespace GlobalTheory.DvrAnyChar

theorem qkToAkU_level_any : LL → AnyUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (k n N : ℕ), 1 ≤ k → 1 ≤ n →
    N = k * n → ∀ (p : QkPt D.toPre F k) (q : QkPt D.toPre F N) x, q.y = n • p.y → q.g = p.g →
    QkToAkU U.toUnifPre F k p x → QkToAkU U.toUnifPre F N q x := by
  intro hL R _ _ I hI D A G _ _ hG U F _ _ _ k n N hk hn hN p q x hy hg hx
  have hN1 : 1 ≤ N := hN ▸ Nat.mul_pos hk hn
  obtain ⟨x₀, h₀⟩ := existsTransl_any hL R I hI D A G hG U F k hk p
  have a := (indAtTransl_any hL R I hI D A G hG U F k hk p x₀).1
    (h₀ 1 k le_rfl (Nat.mul_one k).symm p (one_nsmul _).symm rfl)
  obtain rfl := GlobalTheory.TorsionImage.qkToAkU_unique hL.1 hL.2.1 R I hI D A G hG U F k hk p x x₀ hx a
  exact (indAtTransl_any hL R I hI D A G hG U F N hN1 q x).1 (h₀ n N hn hN q hy hg)

end GlobalTheory.DvrAnyChar
