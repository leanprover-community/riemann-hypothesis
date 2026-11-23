module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStmt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EventuallyIsVacIndicatorK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsVacAnyDarbouxK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsRationalDarbouxOfIsGoodK
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section



section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem modelEx_k : _root_.PositivityTheory.ThKG.Tow.ModelEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := _root_.Tw.RatDarboux.exists_rational_darboux_of_isGood_k B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := _root_.Tw.VacIndic.eventually_isVac_indicator_k B hB X W r s r' s' hX hW co hco
  have hA := _root_.Tw.VacAny.exists_isVac_any_darboux_k B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv
end PositivityTheory.ThKG.Tow
end
end
