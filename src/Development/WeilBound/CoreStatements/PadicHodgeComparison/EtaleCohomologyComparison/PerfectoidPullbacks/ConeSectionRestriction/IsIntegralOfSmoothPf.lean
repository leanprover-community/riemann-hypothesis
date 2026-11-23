module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsAwayIsDomainOfSmooth
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsIntegralNbhd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IrreducibleSpaceOfConnectedOfLocally
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isIntegral_of_smooth_pf {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension n q] : IsIntegral X := by
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth n q
  have hE : ∀ (A : Type) [CommRing A] [Algebra K A] [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime],
      ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S :=
    fun A _ _ _ p _ => CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.exists_away_isDomain_of_smooth (K := K) p
  choose W hxW hW using fun x => CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.exists_integral_nbhd q hE x
  have hcov : TopologicalSpace.IsOpenCover W :=
    eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  have hredi : ∀ i, IsReduced ((X.openCoverOfIsOpenCover W hcov).X i) := by
    intro i
    rw [Scheme.openCoverOfIsOpenCover_X]
    have := hW i
    exact isReduced_of_isIntegral _
  have hred : IsReduced X := IsReduced.of_openCover X (X.openCoverOfIsOpenCover W hcov)
  have hirr : IrreducibleSpace X := by
    refine CrystallineSemistableComparison.Pb.EtaleIntegralityFacts.irreducibleSpace_of_connected_of_locally fun x => ⟨W x, (W x).isOpen, hxW x, ?_⟩
    have := hW x
    have hi := irreducibleSpace_of_isIntegral (W x : Scheme)
    have h2 := (IrreducibleSpace.isIrreducible_univ (↥(W x : Scheme))).image Subtype.val
      continuous_subtype_val.continuousOn
    rwa [Set.image_univ, Subtype.range_coe] at h2
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end CrystallineSemistableComparison.Pb
