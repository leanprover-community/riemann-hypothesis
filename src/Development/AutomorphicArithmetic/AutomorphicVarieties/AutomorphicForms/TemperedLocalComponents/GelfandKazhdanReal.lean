module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.ConjSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairOfTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.PairZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.UnitTwist
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

open NumberField GlobalTheory.CuspRep UpperTheory.V

open GroundTheory.Automorphic in
private theorem lieMatch : UpperTheory.V.Af.Gk.LieMatch := by
  intro F _ _ _ a
  refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ =>
    congrArg Subtype.val (UpperTheory.V.Af.CuspFin.uAction_lieEq X φ)⟩
  rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
  rfl

theorem UpperTheory.V.Af.gelfandKazhdanReal :
    UpperTheory.V.Published.StrongMultOneReal → UpperTheory.V.Published.GelfandKazhdanReal :=
  Gk.gelfandKazhdan_of Gk.conjSub Gk.satConj Gk.satAE Gk.unitTwist Gk.pairOfTwist Gk.pairZero
    (Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) lieMatch)
