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

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.GlobalTheoryTheory.AFTransport

open Formalism.BasicNotions

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def iotaFHom : X.B.I.F →+* D.host.F :=
  (X.ιE.toRingHom.comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F
    (fun a => (X.ιE_F _).2 ⟨a, rfl⟩)

theorem iotaFHom_bijective : Function.Bijective (iotaFHom X) :=
  ⟨(iotaFHom X).injective, fun y => by
    obtain ⟨a, ha⟩ := (X.ιE_F y).1 y.2
    exact ⟨a, Subtype.ext ha⟩⟩

def iotaF : X.B.I.F ≃+* D.host.F := RingEquiv.ofBijective (iotaFHom X) (iotaFHom_bijective X)

theorem iotaF_coe (a : X.B.I.F) : ((iotaF X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

end Formalism.L2.GlobalTheoryTheory.AFTransport
