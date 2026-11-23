module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNeAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InertialTypeOfTameM
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MBlockParamH
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.InertialTypes
theorem main_alt_alt : ∀ (D : D7) (T : WDTie D.nd D.naut) (S : Reading T), TameSplitAll D.host.E → BlockSplitAll D.host.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → ChiIne D.nd D.naut → (∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) → TypeTame S i w hw) → (∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw) → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro D T S hTS hBS hL hS hchi hT hB
  refine ⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩
  · have hw := D.nd.SQ_split i w hSQ
    refine _root_.GlobalTheory.TameType.inertialType_of_tame_m_alt _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_)
      (hchi i w (D.nd.SQ_l i w hSQ)) P
    by_cases hQ : w ∈ D.nd.Q i
    · exact Or.inl hQ
    · refine Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩
      rcases (hc.resolve_left hQ).2 with h | ⟨-, h⟩
      · exact not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h
      · exact not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h
  · have hw := D.nd.SQ_split i w (Or.inl hwS)
    exact _root_.UpperTheory.One.M.split_param_of_typeBlock _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS))
      (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm
end GlobalTheory.InertialTypes
end
