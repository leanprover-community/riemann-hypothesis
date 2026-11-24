module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.FixedConj

def adeleEquiv (D : Formalism.BasicNotions.D7) (hF : D.host.F = maximalRealSubfield D.host.E) :
    ReciprocityTheory.Aut.AL D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (GlobalTheory.StdFrame.tensCastR hF).symm.trans
    (Algebra.TensorProduct.comm (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E).toRingEquiv

def primeComap {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E')
    (w : HeightOneSpectrum (𝓞 E')) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingEquiv ι) w.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv ι)) h
    rwa [Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv ι).surjective, Ideal.map_bot] at this

end GlobalTheory.FixedConj

end
