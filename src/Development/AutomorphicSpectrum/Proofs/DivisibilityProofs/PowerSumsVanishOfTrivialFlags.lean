module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimensionStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
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

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ZTop

theorem isFibreComp_variety {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {W : Ideal (MRing ι O)} (hW : IsFibreComp P W) :
    IsMultiProjPrime (specialIdeal W) ∧
      ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hmin, hrel⟩ := hW
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmin
  refine PairNumberJoinLeft.verticalComponentFibre O ϖ hϖ K ι P d hP (C ϖ) 0
    (isWeightedHomogeneous_C _ _) (fun h => hϖ.ne_zero ?_) W hmin hrel
    (hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_bot.mp (hP.noTorsion ▸ Ideal.mem_comap.mpr h)

theorem cast_classNum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    ((classNum cls H Q W : ℤ) : ℝ) =
      genNum (IsLocalRing.ResidueField O) (specialIdeal W) cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q := by
  unfold classNum genNum
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℝ))]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

theorem powerSumsVanish_of_trivFlagAt :
    NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
      Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ),
      (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  intro hS O _ _ _ ϖ hϖ K _ _ ι _ P d hP N x hx W hW k hk Q hQ
  obtain ⟨Ω, _, _, y, w, hy, hflag⟩ := hx W hW
  obtain ⟨hprime, hdim⟩ := isFibreComp_variety hϖ hP hW
  have h := GlobalTheory.T.flag_frame_point_dimension hS (IsLocalRing.ResidueField O) Ω K ι y d (hy ▸ hprime) (hy ▸ hdim) N w x hflag
    k hk Q hQ
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin N) ℤ k) = ∑ i, X i ^ k := by
    simp [psum]
  have h2 := cast_classNum x (psum (Fin N) ℤ k) Q W
  rw [hmap, ← hy, h] at h2
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Num.ZTop
