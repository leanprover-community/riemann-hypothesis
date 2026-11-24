module

public import Development.WeilBound.ThetaLifts.SmallCones.HodgeTateFromSandwich
public import Development.WeilBound.ThetaLifts.SmallCones.MatCancel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.WeilBound.ThetaLifts.SmallCones.ColsOfMul

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem stabDec_of : StabDec := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have e : fr (incM F H.ι) (incV F H.x) (incV F H.y) = incM F (fr H.ι H.x H.y) := fr_map _
  refine ⟨fun p t hp => ?_, fun ξ g₁ hg m hm => ?_, fun t g₁ m hm u hu => levi_conj hm hu⟩
  · obtain ⟨u, hu, g₁, m, h1, h2, h3⟩ := stab_dec hB.cm h (det_ne hY) p t hp
    refine ⟨u, hu, g₁, m, h1, h2, fun hr => ?_⟩
    obtain ⟨M, hM⟩ := mem_ratU.1 hr
    refine mem_ratU.2 ⟨(A' * M * fr H.ι H.x H.y).toBlocks₁₁, ?_⟩
    rw [h3, hM, e, incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  · obtain ⟨m', h1, h2⟩ := exists_levi hB.cm h (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁
    obtain ⟨M, hM⟩ := mem_ratU.1 hg
    rw [levi_uniq h hm h1]
    refine mem_ratU.2 ⟨fr H.ι H.x H.y * dg M ξ.1 (σ (ξ⁻¹).1) * A', ?_⟩
    rw [h2, hM, e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext (i | i) (j | j)
    · rfl
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · fin_cases i <;> fin_cases j
      exacts [rfl, (map_zero (inclR (F := F) (E := E) (AF F))).symm, (map_zero (inclR (F := F) (E := E) (AF F))).symm, rfl]

end PositivityTheory.ThKCT

end
