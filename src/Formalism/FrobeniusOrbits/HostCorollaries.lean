module

public import Formalism.FrobeniusOrbits.Statement
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CardTrivialFirstComponent
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ConjReal
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Decomp
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.FrobMulInertia
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Inertia
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace Formalism.FrobeniusOrbits.Final

open Formalism.FrobeniusOrbits

theorem conj : HostConj := hostConj_of hostGalois hostGalSpec
theorem real : HostReal := hostReal_of hostGalois hostGalSpec conj
theorem f1 : TwoPowerCyclotomicLayerRealSubfieldCharacterization := real_subfield_of_galois_spec hostGalSpec
theorem cmType : HostCMType := hostCMType_of hostGalois hostGalSpec
theorem frob : HostFrob := hostFrob_of hostGalois hostGalSpec
theorem splitK : HostSplitK := hostSplitK_of (hostFrob_of hostGalois hostGalSpec)
theorem efgTwo : HostEFGTwo := hostEFGTwo_of hostInertia hostDecomp

theorem host_field :
    HostExample ∧ HostGroup ∧ HostOrders ∧ HostRecip ∧ HostFixed ∧ HostGalois ∧ HostGalSpec ∧
    HostConj ∧ HostReal ∧ TwoPowerCyclotomicLayerRealSubfieldCharacterization ∧ HostMu ∧ HostFrob ∧ HostInertia ∧ HostUnramEF ∧
    HostDecomp ∧ HostDecompConj ∧ HostEFGTwo ∧ HostSplitK ∧ HostCMType :=
  ⟨hostExample, hostGroup, hostOrders, hostRecip, hostFixed, hostGalois, hostGalSpec, conj, real, f1, hostMu,
    frob, hostInertia, hostUnramEF, hostDecomp, hostDecompConj, efgTwo, splitK, cmType⟩

end Formalism.FrobeniusOrbits.Final
