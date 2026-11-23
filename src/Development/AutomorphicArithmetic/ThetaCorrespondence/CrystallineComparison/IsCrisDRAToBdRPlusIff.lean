module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IsCrisDRAIff
public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (Ideal.span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

theorem isCrisDRA_toBdRPlus_iff (f : Bcris p R →+* BdR p R) :
    IsCrisDRA (Acris.toBdRPlus p R) f ↔ f = Bcris.toBdR p R := by
  constructor
  · intro hf
    refine Bcris.hom_ext fun x => ?_
    have h := BcrisPlus.hom_ext (f := f.comp (algebraMap (BcrisPlus p R) (Bcris p R)))
      (g := (Bcris.toBdR p R).comp (algebraMap (BcrisPlus p R) (Bcris p R))) (fun y => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply, hf y, Bcris.toBdR_algebraMap_acris])
    exact RingHom.congr_fun h x
  · rintro rfl x
    exact Bcris.toBdR_algebraMap_acris x

end Formalism.BasicNotions.CmpTie.Incl
