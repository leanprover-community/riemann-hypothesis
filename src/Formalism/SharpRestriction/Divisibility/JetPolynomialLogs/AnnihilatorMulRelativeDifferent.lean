module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
public import Formalism.DirichletDensity.HostDensityArith
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.placeRankTwoOne NumberField Formalism.FrobeniusOrbits
open scoped Pointwise

namespace Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent

theorem discr_K (D : D7) : discr D.host.K = -(D.host.d : ℤ) := by
  have hb : D.host.sqd ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  let x : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hx : x ^ 2 = ((-(D.host.d : ℤ) : ℤ) : D.host.K) := by
    apply Subtype.ext
    simpa [x] using hb
  have htop : IntermediateField.adjoin ℚ {x} = ⊤ := by
    apply Formalism.HF.P.adjoin_top_of_lift
    rw [Set.image_singleton]
    rfl
  exact Formalism.HF.Final.quadDiscr D.host.K _ x hx htop (Formalism.HF.P.sqf_neg _ D.host.hyp.2.1)
    (by have := D.host.hyp.2.2.2.1; omega)

theorem finrank_K (D : D7) : Module.finrank ℚ D.host.K = 2 :=
  SplitK.finrank_K (L := D.host.E) (b := D.host.sqd) (d := D.host.d) D.host.hyp.2.1.pos
    (D.host.sqd_sq)

end Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent
