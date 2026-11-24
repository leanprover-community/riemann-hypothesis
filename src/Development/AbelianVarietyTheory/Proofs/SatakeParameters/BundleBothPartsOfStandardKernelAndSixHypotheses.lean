module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowAtOfStdTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowTwUHolds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueCStatement
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem servH_row (hA : Formalism.L2.KerInert.AlgTAll) (hG : Formalism.L2.KerInert.GenusOneModelExistsLattice) (hC : Formalism.L2.KerInert.Rep.CurveDict)
    (hI : Formalism.L2.KerInert.IntInert) (hE : GlobalTheory.TwV.Lt.AdmAtEnt2) (hX : GlobalTheory.TwV.Lt.CurveEx) :
    ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex),
      (∀ K X f T c, Q K X f T c → positionOf HasPart K X f T c) →
      RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (ServH ker) := by
  intro Bd Q Lk ker hQ hT
  have hM : RowE Q Lk (fun _ D O _ _ => ModelsAt D O) :=
    RowE.of_all fun _ K β _ _ _ hq _ => GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns hE hX K β (hQ _ _ _ _ _ hq)
  exact Row.and (GlobalTheory.Svd.rowTwU Q Lk hM) (GlobalTheory.Pdv.rowAt_of_stdTie hA hG hC hI Q Lk ker hT)

end GlobalTheory.Svd
