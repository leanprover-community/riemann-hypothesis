module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.NumberTheory.Padics.Complex
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
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.Primes
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable (D : D7)

variable {p : ℕ} [hp : Fact p.Prime]

section Kstr

variable (D : D7)

end Kstr

section PadicK

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

end PadicK

section Alg

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

end Alg

section Lat

variable {D : D7} {N N' : ℕ}

end Lat

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP


section Tor0

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}




end Tor0

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP


section Sums

end Sums

section Main

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

end Main

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP


section StepA

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}


end StepA

section StepC

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}


end StepC

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP


variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

end Formalism.L2.PairingIndexBounds.Xf.XiOneP
