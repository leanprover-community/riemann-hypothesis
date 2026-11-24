module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigRMemOAd
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G.IotaSigmaCompatibility

theorem iotaA_sigA : ∀ (D : D7) (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA →
    ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  intro D X ιA h a
  have he : ∀ x : X.B.I.E, X.ιE (X.B.I.cm.sig x) = Formalism.L2.Forms.sigD D (X.ιE x) := by
    intro x
    have h1 : X.B.I.cm.sig x = star x := rfl
    have h2 : Formalism.L2.Forms.sigD D (X.ιE x) = star (X.ιE x) := rfl
    rw [h1, h2, X.ιE_conj, Formalism.BasicNotions.bridge_star_holds D.R D.host]
  exact GlobalTheory.St.G.IotaConj.iota_sigR X.B.I.F X.B.I.E D.host.F D.host.E X.B.I.cm.sig
    (Formalism.L2.Forms.sigD D) X.ιE ιA he h.1 h.2 a

end GlobalTheory.St.G.IotaSigmaCompatibility
