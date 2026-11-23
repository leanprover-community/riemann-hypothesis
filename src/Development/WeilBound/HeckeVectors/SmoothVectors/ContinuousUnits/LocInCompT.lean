module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open GlobalTheory.CuspRep

namespace CompanionTheory.D.gk.Br.LIC

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem continuous_infGL [_root_.NumberField.IsTotallyComplex E] : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem continuous_finGL : Continuous (finGL E a) := by
  have hs : Continuous (sFin E) := (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sFin E))) (continuous_const.add (continuous_id.matrix_map hs))


omit [NumberField E] in
theorem continuous_toUnits_Kinf : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E)) :=
  Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩

theorem continuous_infGL_toUnits [_root_.NumberField.IsTotallyComplex E] :
    Continuous fun k : Kinf E a => infGL E a (Unitary.toUnits k) :=
  continuous_infGL.comp continuous_toUnits_Kinf

end CompanionTheory.D.gk.Br.LIC
