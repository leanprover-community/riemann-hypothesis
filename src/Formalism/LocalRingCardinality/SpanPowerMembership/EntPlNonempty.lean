module

public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis
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

@[expose] public section

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

structure EntPl (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_lam : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x)
  iL_lam' : ∀ w x (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ), iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

theorem entPl_nonempty (D : D7) : Nonempty (EntPl D) := by
  choose lam iL h1 h2 using fun w => exists_placeEmb D w
  exact ⟨⟨lam, iL, fun w x => by
    obtain ⟨hx, e⟩ := h1 w x
    rw [lamV, dite_eq_left hx, e], fun w x _ => (h1 w x).choose_spec, h2⟩⟩

end Formalism.BasicNotions.Examples₂
