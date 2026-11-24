module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
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
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1
theorem row_hServ_of_kerServ_alt : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    Row Q Lk (GlobalTheory.Svd.ServH fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => b.R.T.ker) → _root_.GlobalTheory.Fc.R1.SlotServiceCondition Q Lk := by
  intro Q Lk h
  refine Row.imp h fun 𝒜 σ _ hs => ?_
  obtain ⟨⟨a, ha, hK⟩, hA⟩ := hs
  refine ⟨⟨a, ha, fun e he hle => ?_⟩, ⟨a, ha, fun e he hle => ?_⟩⟩
  · obtain ⟨K, hK⟩ := hK e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (GlobalTheory.Cp.d3_a hc) hL⟩
  · obtain ⟨K, _⟩ := hK e he hle
    exact ⟨K, fun Fm _ _ _ hc x hx _ i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i⟩
end GlobalTheory.Fc.R1
end
