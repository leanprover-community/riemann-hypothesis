module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraTail
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerSide
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerLast
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

section Zero

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem X_mem_primeOf_of_eq_zero {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Kleiman.Poly S N) ∈ Kleiman.primeOf (S := S) x := by
  rw [Kleiman.primeOf_eq, RingHom.mem_ker]
  simp [Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hi]

theorem X_base_mem_mIdealOver_graph (s : Fin m → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) S) ∈ mIdealOver S (graphVec x s) := by
  change mConeMapOver S (graphVec x s) (X _) = 0
  simp [mConeMapOver]
  exact hi

end Zero

theorem NefEq.proof (hC : CurveComap.Statement) (hL : CurveLift.Statement) (hD : DegEq.Statement) :
    NefEq.Statement := by
  intro k _ N Ω _ _ x Q n m s hgen
  by_cases hx : ∃ i, x i ≠ 0
  · constructor
    · intro hnef W hW hle hrel
      have hsub := (hC k N Ω x Q n m s hx hgen W hW hle 1).mp hrel
      rw [hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef _ bot_le hsub
    · intro hnef pp _ hsub
      obtain ⟨W, hW, hle, rfl⟩ := hL k N Ω x Q n m s hx hgen pp 1 hsub
      rw [← hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef W hW hle ((hC k N Ω x Q n m s hx hgen W hW hle 1).mpr hsub)
  · push Not at hx
    constructor
    · intro _ W hW hle _
      exfalso
      obtain ⟨i, hi⟩ := hW.relevant baseBlock
      exact hi (hle (X_base_mem_mIdealOver_graph s (hx i)))
    · intro _ pp _ hsub
      exfalso
      obtain ⟨i, hi⟩ := hsub.relevant
      exact hi (hsub.le (X_mem_primeOf_of_eq_zero (hx i)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
