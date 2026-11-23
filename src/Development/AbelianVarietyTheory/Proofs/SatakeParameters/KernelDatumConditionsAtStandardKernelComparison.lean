module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AtOfTrueColumns
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepRepEqOneAtTypePrimes
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

namespace GlobalTheory.PdvTie

theorem at_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ (D : D7) (O : Obj D) (t : KerEntTied O.ex), StdTie D O t → 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 → (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) → GlobalTheory.Pdv.At O.ex t.ent := by
  intro hA hG hC hI D O t hT hs h1 h2 hE
  refine StdTie.ind (R := fun D O t => 3 ≤ D.host.splitBound → 5 ≤ O.K.dl1 → 4 ≤ O.K.dl2 →
      (∀ Ee : OrbitPlaces.Ent D, OrbitPlaces.Shape D O.L O.Gx Ee ∧ ∀ u, ∀ j < D.R.m, ∀ s ∈ D.host.TT, Ee.row u j (false, s) 0 - Ee.row u j (false, s) 1 ≤ 2 * O.L.sc.a) →
      GlobalTheory.Pdv.At O.ex t.ent) ?_ hT hs h1 h2 hE
  intro B X I l l0 Z O t h hs h1 h2 hE
  exact GlobalTheory.PdvClose.at_of_true_columns hA hG hC hI I h.ok h.pins l Z l0 O.L O.gatT O.Gx O.Gy O.K O.X O.cX O.ex t
    (GlobalTheory.Pdv.colNorm_of_tw I h.isTw) h.jets h.tw h.ker h.entC h.adapted h.top hs h1 h2 hE

end GlobalTheory.PdvTie
