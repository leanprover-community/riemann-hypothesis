module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtAllStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJointsStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_of_part : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (O : Obj (w.D Z)), Part w Z (ofObj O) → ModelsAt (w.D Z) O := by
  intro hA hC B f T w Z O hP hL hk
  obtain ⟨⟨t, hJ⟩, he⟩ := GlobalTheory.Svd.jointsAt_all_std B f T w Z O hP hL
  have hS : OrbitPlaces.Stab0 (w.D Z) := GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns w.I w.ok w.pins w.l Z O.ex.lev
  exact GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints hA hC t (fun μ _ => hJ μ) he hS hk

end GlobalTheory.Svd
