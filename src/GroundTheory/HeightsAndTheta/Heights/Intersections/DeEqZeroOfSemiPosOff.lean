module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {n : ℕ}
  {A A' : HermLine ι} {s s' : MRing ι}

theorem De_eq_zero_of_semiPos (hLe : DeLeSemiPos.Statement) {L : Fin n → HermLine ι}
    (hP : IsArithVar P (n + 2)) (hL : ∀ j, IsSmoothHerm (L j)) (hLp : ∀ j, IsSemiPosHerm (L j))
    (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) :
    De P L A A' s s' = 0 := by
  have h1 := hLe K ι P n L A A' s s' hP hL hLp hA hA' hs hs' hnc
  have h2 := hLe K ι P n L A' A s' s hP hL hLp hA' hA hs' hs (fun W h h' => hnc W h' h)
  rw [De_swap] at h2
  linarith

theorem De_eq_zero_of_semiPos_off (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) (hP : IsArithVar P (n + 2)) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (hs : IsSectionOn P A s) (hs' : IsSectionOn P A' s')
    (hnc : ∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) (S : Finset (Fin n)) :
    ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) → (∀ j, j ∉ S → IsSemiPosHerm (L j)) →
      De P L A A' s s' = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro L hL hLp
    exact De_eq_zero_of_semiPos hLe hP hL (fun j => hLp j (Finset.notMem_empty j)) hA hA' hs hs' hnc
  | @insert j S hj ih =>
    intro L hL hLp
    obtain ⟨T, hT, hTp, hLTp⟩ := hTw K ι (L j) (hL j)
    have hadd := hAdd K ι P n L j (L j) T A A' s s' hP hL (hL j) hT hA hA' hs hs' hnc
    rw [Function.update_eq_self] at hadd
    have hsm : ∀ X : HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
      intro X hX i
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hL i
    have hpos : ∀ X : HermLine ι, IsSemiPosHerm X → ∀ i, i ∉ S →
        IsSemiPosHerm (Function.update L j X i) := by
      intro X hX i hi
      rcases eq_or_ne i j with rfl | hij
      · simpa using hX
      · rw [Function.update_of_ne hij]
        exact hLp i (by simp [Finset.mem_insert, hij, hi])
    rw [ih _ (hsm _ (isSmoothHerm_tensor (hL j) hT)) (hpos _ hLTp),
      ih _ (hsm _ hT) (hpos _ hTp)] at hadd
    linarith

theorem ProjectiveLineTwo.proof (hAdd : DeSlotAdd.Statement) (hTw : SemiPosTwist.Statement)
    (hLe : DeLeSemiPos.Statement) : SectionSpaceSymmetry := by
  intro K _ ι _ P n L A A' s s' hP hL hA hA' hs hs' hnc
  have h := De_eq_zero_of_semiPos_off hAdd hTw hLe hP hA hA' hs hs' hnc Finset.univ L hL
    (fun j hj => absurd (Finset.mem_univ j) hj)
  unfold De at h
  linarith

end GroundTheory.Heights₂.Heights.Inter
