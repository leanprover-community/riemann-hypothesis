module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.HostUnramP

open NumberField IsDedekindDomain Formalism.BasicNotions

def HostUnramG : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∀ (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2),
    ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal → ((D.host.g i : ℕ) : 𝓞 D.host.F) ∉ p.asIdeal ^ 2

theorem gi_val (D : D7) (p : HeightOneSpectrum (𝓞 D.host.F)) (i : Fin 2)
    (hi : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) :
    p.intValuation ((D.host.g i : ℕ) : 𝓞 D.host.F) = WithZero.exp (-1 : ℤ) := by
  exact Formalism.L2.SG.Pf.TypedLoc.tower_val D.host.F D.host.E (D.host.g_prime i) (D.nd.g_split i) p hi

theorem hostUnramG : HostUnramG := by
  intro D _ p i hi hsq
  have h2 := (p.intValuation_le_pow_iff_mem _ 2).mpr hsq
  rw [gi_val D p i hi] at h2
  have h3 := WithZero.exp_le_exp.mp h2
  omega

end Formalism.L2.SG.Pf.HostUnramP
