module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeMaxCpt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRatPts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

namespace Formalism.L2.SG.Closed

theorem AdBridgeIso_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeIso I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_exists (I := I)

theorem AdBridgeGF_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeGF I := adelic_rational_points I

theorem AdBridgeK_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeK I := adelic_maximal_compact I

theorem adelic_isomorphism_statement (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdelicIsomorphism I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_of_parts (I := I) (adelic_rational_points I) (adelic_maximal_compact I)

end Formalism.L2.SG.Closed
