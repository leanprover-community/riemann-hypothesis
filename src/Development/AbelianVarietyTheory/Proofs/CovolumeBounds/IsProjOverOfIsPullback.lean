module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG IsProjOver)
namespace GlobalTheory.ProjSpace

theorem isProjOver_pspace_str (R : Type) [CommRing R] (N : ℕ) : IsProjOver (PSpace.str R N) :=
  ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩

theorem isProjOver_of_isPullback {R : Type} [CommRing R] {X Y Z : Scheme.{0}} {p : Z ⟶ X} {q : Z ⟶ Y}
    {f : X ⟶ Sp R} {g : Y ⟶ Sp R} (sq : IsPullback p q f g) (hf : IsProjOver f) (hg : IsProjOver g) :
    IsProjOver (p ≫ f) :=
  (isProjBy_iff_isProjOver _).1 (GlobalTheory.AbLaw.Segre.isProjBy_of_isPullback p q sq
    ((isProjBy_iff_isProjOver f).2 hf) ((isProjBy_iff_isProjOver g).2 hg))

theorem isProjOver_pullback_str (R : Type) [CommRing R] (N M : ℕ) :
    IsProjOver (pullback.fst (PSpace.str R N) (PSpace.str R M) ≫ PSpace.str R N) :=
  isProjOver_of_isPullback (IsPullback.of_hasPullback _ _) (isProjOver_pspace_str R N)
    (isProjOver_pspace_str R M)

end GlobalTheory.ProjSpace
