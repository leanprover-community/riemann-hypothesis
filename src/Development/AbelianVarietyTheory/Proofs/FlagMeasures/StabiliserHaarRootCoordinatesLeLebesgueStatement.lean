module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  first | exact @GlobalTheory.LoopVol.pinned_ratCoord_le | exact GlobalTheory.LoopVol.pinned_ratCoord_le | (intros; apply GlobalTheory.LoopVol.pinned_ratCoord_le <;> assumption)
