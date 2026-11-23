module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLabelWeightsOfGreenCuspidalParametrisa
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkIRROfJoinEx
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
import Mathlib.Tactic.NormNum.Prime
import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section



section
noncomputable section
namespace GlobalTheory.Top.Irr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.ConcNWeight Formalism.L2.GlobalTheoryTheory.AllJoin
end
section
open Formalism.BasicNotions Formalism.MainNotions
end
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4
theorem closed_linkIRR_of_join_count : GlobalTheory.GLq.Green → ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (cIc : ℝ)
    (hcI : 0 < cIc)
    (irrC : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f)), Closed (D3 3 𝒜) fun Fm _ => LinkIRR Fm := by
  intro hG 𝒜 sel cIc hcI irrC
  have irr : Closed (D3 3 𝒜) fun {eps} Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : Formalism.MainNotions.ArithmeticCylinders.AllRows (Fm.D x i),
      Formalism.MainNotions.ArithmeticCylinders.LabelCountGoodInjective A ∧ Formalism.L2.GlobalTheoryTheory.AllJoin.AllJoinA A ∧ Formalism.MainNotions.ArithmeticCylinders.admLq (Fm.D x i) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.CountAllRows A (Formalism.L2.GlobalTheoryTheory.ConcN.epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) ∧
        Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec (Fm.D x i) x Fm.ez 6 :=
    closed_of_mem (irrC.imp fun Fm _ _ H hc => by
      obtain ⟨x0, H⟩ := H
      refine ⟨max (max x0 (sel Fm (d3_a hc)).1) (max (Fm.x1 + 1) 4), fun x hx i => ?_⟩
      have h1 : Fm.x1 < x := by have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx; linarith
      have hs : (sel Fm (d3_a hc)).1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
      obtain ⟨A, a, b, c⟩ := H x (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx) i
      exact ⟨A, a, b, GlobalTheory.Top.Lq.admissibleLabelWeights_of_greenCuspidalParametrisation hG _ _ ((sel Fm (d3_a hc)).2 x h1 hs i).T.n.types, c,
        sizesRec_at Fm h1 (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) i le_rfl⟩)
  exact (irr.and (closed_eps_le_one _)).imp fun Fm _ he ⟨h, h1⟩ =>
      linkIRR_of_join_ex _ 6 cIc he h1 hcI Fm h
end GlobalTheory.Top.Irr
end
end
