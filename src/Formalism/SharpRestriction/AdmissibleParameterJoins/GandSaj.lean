module

public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSx
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem sgAtG_of {K : Consts} {lev : LevelData D} {Xe : ErrX D} {ce : ErrC} {C1 : ℝ} (hF : L.FDef)
    (hE : ErrDefs D L Xe lev K ce) (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ ce.g) : Formalism.MainNotions.WeightDegreeSizes.SgAtG D L Xe C1 :=
  fun i w hwi u hw => sumFE_atG_le hF hE hC1 hC i w hwi u hw

theorem family_type_prime_loss {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {C1 : ℝ} (hC1 : 0 ≤ C1) (hC : 2 * C1 ≤ Fm.cX.err.g) :
    Formalism.MainNotions.WeightDegreeSizes.familySizeBoundAtTypePrime Fm C1 :=
  ⟨0, fun x hx _ i => sgAtG_of (local_compatibility_family Fm x hx i).fdef (Fm.ex x hx i).err hC1 hC⟩

end Formalism.MainNotions.J

end
