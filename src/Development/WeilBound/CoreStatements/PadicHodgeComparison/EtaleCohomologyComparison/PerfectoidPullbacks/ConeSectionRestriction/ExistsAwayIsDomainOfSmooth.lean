module

public import Mathlib.RingTheory.Smooth.Basic
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsTmulOneEqOfIsIntegral
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
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

theorem exists_away_isDomain_of_smooth {K A : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime] :
    ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S := by
  obtain ⟨g, hg, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  obtain ⟨ι, σ, _, _, ⟨Pr⟩⟩ := hstd.out
  haveI : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension K (Localization.Away g) :=
    ⟨⟨ι, σ, ‹_›, ‹_›, Pr, rfl⟩⟩
  obtain ⟨φ, hφ⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    (n := Pr.dimension) (R := K) (S := Localization.Away g)
  letI : Algebra (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := φ.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin Pr.dimension) K) (Localization.Away g) := hφ
  haveI hq : (p.map (algebraMap A (Localization.Away g))).IsPrime := by
    apply IsLocalization.isPrime_of_isPrime_disjoint (.powers g) _ _ ‹_›
    rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
  obtain ⟨g', hg', hdom⟩ := exists_away_isDomain_of_etale
    (P := MvPolynomial (Fin Pr.dimension) K) (A := Localization.Away g)
    (p.map (algebraMap A (Localization.Away g)))
  refine ⟨g * (IsLocalization.Away.sec g g').1, ?_, ?_⟩
  · refine Ideal.IsPrime.mul_notMem ‹_› hg fun hmem => hg' ?_
    rw [Ideal.mem_iff_of_associated (IsLocalization.Away.associated_sec_fst g g').symm]
    exact Ideal.mem_map_of_mem (algebraMap A (Localization.Away g)) hmem
  · intro S _ _ _
    haveI : IsLocalization.Away (g * (IsLocalization.Away.sec g g').1) (Localization.Away g') :=
      .mul_of_associated _ _ g' <| IsLocalization.Away.associated_sec_fst g g'
    let e : S ≃ₐ[A] Localization.Away g' :=
      IsLocalization.algEquiv (Submonoid.powers (g * (IsLocalization.Away.sec g g').1)) S
        (Localization.Away g')
    exact e.toRingEquiv.toMulEquiv.isDomain

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
