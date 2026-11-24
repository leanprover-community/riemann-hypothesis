module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfSplitLat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.DenomHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfParts
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

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting

theorem latBasisAll_holds {D : D7} (X : HidaSetting D) (p : TypX X) : LatBasisAll X p := by
  apply latBasisAll_of_parts
  · intro θ hθ
    exact denom_holds (X := X) (p := p) (θ := θ) hθ
  · intro θ hθ
    exact approx_of (X := X) (p := p) (θ := θ) hθ (denseF_holds X p) (epsLat_holds X p θ)

theorem stRed_of_embP {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) : StRed X p :=
  stRed_of_emb X p hE (latBasisAll_holds X p)

end MassDataIdxSteps
