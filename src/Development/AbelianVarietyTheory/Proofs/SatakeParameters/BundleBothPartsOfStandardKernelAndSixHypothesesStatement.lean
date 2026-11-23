module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelAndSixHypotheses
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.bundle_bothParts_of_standardKernel_and_six_hypotheses : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) → RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  exact @GlobalTheory.Svd.servH_row
