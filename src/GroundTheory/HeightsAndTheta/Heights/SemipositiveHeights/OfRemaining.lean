module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyBridgeFull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SiuZB.proof (hK : KodairaGeneric.Statement) (hZ : SectionsDimZero.Statement) : KH.SiuZStatement := by
  intro K _ ι _ Ω _ _ y D α I hI hV hB hNef hPos
  classical

  have hagree : ∀ (V : Ideal (MRingOver ℚ ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum ℚ V L := by
    obtain ⟨I₀, -, h₀⟩ := Targets.ExistsUnique.full ℚ ι
    intro V n L hVn
    rw [h₀ I hI V n L hVn, h₀ _ (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) V n L hVn]
  have hG : IsProjVarF (KH.genIdeal y) D := isProjVarF_map_of_isArithVar hV
  have hdeg : 0 < genDeg (mCoordIdeal y) D α := by
    have h := hagree _ D (fun _ => α) hG
    rw [h] at hPos
    exact hPos

  obtain ⟨k, e, hk, he, hmem⟩ :
      ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • α - 1) 1 := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have hr := hZ K ι Ω y ((1 : ℕ) • α - 1) 1 hV
      have hg : genDeg (mCoordIdeal y) 0 ((1 : ℕ) • α - 1) = genDeg (mCoordIdeal y) 0 α := by
        unfold genDeg
        congr 1
        funext j
        exact j.elim0
      rw [hg] at hr
      have hpos : 0 < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by
        have : (0 : ℤ) < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by rw [hr]; exact hdeg
        exact_mod_cast this
      have := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (0 : chartLatQ y ((1 : ℕ) • α - 1) 1)
      refine ⟨1, e, le_rfl, fun h => hne ?_, by simpa using he⟩
      exact Subtype.ext h
    · have hnef : NefOnGenericDeg (mCoordIdeal y) α := by
        intro W hW hPW
        have hWq : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
          isProjVarF_map_of_isArithVar (D := 1) hW
        have h := hNef _ hWq (Ideal.map_mono hPW)
        rw [hagree _ 1 _ hWq] at h
        unfold genDeg
        convert h using 2
        funext j
        fin_cases j
        rfl
      exact hK K ι Ω y D α hD hV hB hnef hdeg

  obtain ⟨n, hn, hns⟩ := ChartDenominator.proof K ι Ω y ((k : ℤ) • α - 1) 1 e hmem
  have hn0 : (n : Ω) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨k, hk, (n : Ω) * e, ?_, mul_ne_zero hn0 he⟩
  have hfun : (fun κ => (k : ℤ) * α κ - 1) = (k : ℤ) • α - 1 := by
    funext κ
    simp
  rw [hfun]
  exact hns

theorem SiuZB.of_kodaira (hK : KodairaGeneric.Statement) : KH.SiuZStatement :=
  SiuZB.proof hK SectionsDimZero.proof

end GroundTheory.Heights₂.Heights.ForSecondHalf
