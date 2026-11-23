module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Assembly
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FundamentalDomainOfCompactOpen
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

open Formalism.L2.SG.TypedSets

theorem massDataMasses_of' (hH : MassDataMassesW.HinfCompact) (hK : MassDataMassesW.KCompactOpen)
    (hC : MassDataMassesW.ClassFinite) (hSA : MassDataMassesW.StrongApproxN) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataMassesW.massDataMasses_of_strongApprox hH hK hC hSA (MassDataMassesW.fundamental_domain_of_compact_open hK MassDataMassesW.nRatBridge_holds)
