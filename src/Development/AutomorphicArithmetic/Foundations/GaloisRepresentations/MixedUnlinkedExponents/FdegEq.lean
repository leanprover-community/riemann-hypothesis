module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.ValsExtOf
import GroundTheory.GlobalFields.KummerTheory.Splitting
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

noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global.SemiLocal UpperTheory.V.Z.Gam

namespace UpperTheory.Gal.GamX

theorem fdegEq : FdegEq := by
  intro K L _ _ _ _ _ _ v
  refine ⟨GroundTheory.Global.nonempty_placesOver L v, fun w w' => ?_⟩
  have hw := w.2
  have hw' := w'.2
  unfold fdeg
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w.1.asIdeal,
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal w'.1.asIdeal]
  exact Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal w.1.asIdeal w'.1.asIdeal Gal(L/K)

end UpperTheory.Gal.GamX
