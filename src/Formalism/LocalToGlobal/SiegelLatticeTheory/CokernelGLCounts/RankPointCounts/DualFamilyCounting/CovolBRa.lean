module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
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

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def aaLbS (b : Fin D.R.rS) : Submodule (𝓞 D.host.E) (VS D).V :=
  Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l}

def TrDetUnimod : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (b : Fin D.R.rS) {N : ℕ}
    (m : Module.Basis (Fin N) ℤ ((aaLbS X b).restrictScalars ℤ)),
    N = Module.finrank ℚ D.host.E * (D.R.k + 1) →
    |(Matrix.of fun i j => Algebra.trace ℚ D.host.E ((VS D).hT (m i : (VS D).V) (m j : (VS D).V))).det| =
      |(discr D.host.E : ℚ)| ^ (D.R.k + 1) * (FractionalIdeal.absNorm (aaD D b) : ℚ) ^ (2 * (D.R.k + 1))

end Formalism.L2.SG.Pf.NcReal.JX.CovB
