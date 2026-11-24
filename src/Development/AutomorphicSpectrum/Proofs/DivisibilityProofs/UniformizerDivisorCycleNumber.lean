module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyCN
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ConsPoly

theorem length_classList {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  rw [← h]
  simp [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply, Finsupp.sum]

theorem cycList_const {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hM : IsModelOver P l.length) (u : Oˣ) (e : ℕ) :
    cycList (divCycle P (C ((u : O) * ϖ ^ e))) l =
      (e : ℤ) * intNumL (FractionRing O) (genFib P) l := by
  haveI : P.IsPrime := hM.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P := by
    intro a ha hmem
    apply ha
    have ha' : a ∈ P.comap (C : O →+* MRing ι O) := Ideal.mem_comap.2 hmem
    rw [hM.noTorsion] at ha'
    exact Ideal.mem_bot.1 ha'
  have hfin := ScalarQuotient.divCycle_support_finite P (C ϖ)
  have key : cycEval (fun W => vNumL W l) (divCycle P (C ϖ)) =
      intNumL (FractionRing O) (genFib P) l :=
    ConservationOfNumber.full O ϖ hϖ K ι P l.length hM l.get
  unfold cycList
  rw [ScalarQuotient.divCycle_const P hC hϖ.ne_zero u e, ← key]
  unfold cycEval
  show ∑ᶠ W, ((e : ℤ) * divCycle P (C ϖ) W) * vNumL W l =
    (e : ℤ) * ∑ᶠ W, divCycle P (C ϖ) W * vNumL W l
  rw [mul_finsum]
  · exact finsum_congr fun W => by ring
  all_goals exact hfin.subset (Function.support_mul_subset_left _ _)

end GlobalTheory.CompanionTheory.Ar.Num.ConsPoly


open GlobalTheory.CompanionTheory.Ar.Num.ConsPoly in
theorem GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hM u e σ cls H m hH Q hd
  unfold cycNum genNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : (classList cls μ ++ Q).length = d := by
    rw [List.length_append, GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.length_classList cls hH hμ, hd]
  have hM' : IsModelOver P (classList cls μ ++ Q).length := by
    rw [hlen]
    exact hM
  rw [GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.cycList_const hϖ _ hM' u e]
  push_cast
  ring
