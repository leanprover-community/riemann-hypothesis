module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NVolAllOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.CountableRatOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassDataMassesOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassHNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SplitG
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

namespace MassDataMassesW

theorem massDataMasses_of_strongApprox (hH : HinfCompact) (hK : KCompactOpen) (hC : ClassFinite) (hSA : StrongApproxN)
    (h3 : UnipotentFundamentalDomain) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataMasses_of (massAll_of hH hK hC) (nVolAll_of hSA splitIso_holds h3 (elliptic_centralizer_quotient_compact hK) n4cov_holds)

end MassDataMassesW
