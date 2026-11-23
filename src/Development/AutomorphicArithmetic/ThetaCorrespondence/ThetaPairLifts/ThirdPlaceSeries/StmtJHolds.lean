module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamFamilyAway
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JumpLemmaAOfAdmissible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section HC
variable {R : Ranks} (P : HCParam R)
end HC
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section JB
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end JB
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
variable {D : D7}
section Core
variable {L : SizeData₂ D} {j : ℕ} {ρ : D.what₂.Tau}
end Core
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Classical
variable {D : D7}
end GlobalTheory.JumpSets
end
noncomputable section
namespace GlobalTheory.JumpSets
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.AdmissibleParameterJ
theorem stmtJ_holds_alt (D : D7) : _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := by
  intro L hA
  obtain ⟨hG2, hCr, hG2g, hDi, hRd, hP⟩ := hA
  have hF : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ρ, JFacts L j ρ := fun j h1 h2 ρ => jFacts_of hP j h1 h2 ρ
  have hpar : L.etaSz + D.R.t + L.Sc ≤ L.sc.b := by
    have := L.Sc_pos; have := L.etaSz_pos
    have : (0 : ℝ) ≤ D.R.t := by positivity
    linarith [hP.1, hP.2.1]
  exact ⟨_root_.GlobalTheory.JumpSets.jumpLemma_a_of_admissible_alt_alt hP hG2 hCr hG2g hDi hRd, jumpSetBound_of_realPlaceFacts hF, jumpSetCloud_of_realPlaceFacts hF, jumpSetDistinct_of_realPlaceFacts hF,
    jumpSetEta_of_realPlaceFacts hF hpar D.R.t_odd.pos L.Sc_pos L.etaSz_pos, jumpSetFinal_of_realPlaceFacts hF, jumpSetGap_of_realPlaceFacts hF⟩
end GlobalTheory.JumpSets
end
end
