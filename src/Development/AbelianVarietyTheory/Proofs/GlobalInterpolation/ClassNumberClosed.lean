module

public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.ColClassNumber

open Formalism.MainNotions

theorem classNumber_closed (𝒞 : FamClass) :
    Closed 𝒞 fun Fm _ => ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLattice.ClassNumberFormula₂ (Fm.D x i) (Fm.ex x hx i).lev :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩,
    fun Fm _ _ _ x hx i => classNumber_all (Fm.D x i) (Fm.ex x hx i).lev⟩⟩

end GlobalTheory.ColClassNumber
