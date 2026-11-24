module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.Padics.Complex
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
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SemiChar

@[expose] public section

noncomputable section

namespace GlobalTheory.Klein

open Formalism.L2.Th1.F
open scoped ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

def Good (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : Prop :=
  p ≠ 2 ∧ ‖ι (12 * r)‖ ≤ 1 ∧ ‖ι (12 * r ^ 2 - L.g₂)‖ ≤ 1 ∧ ‖ι (4 * r ^ 3 - L.g₂ * r - L.g₃)‖ ≤ 1 ∧
    ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1

def Red (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r z : ℂ) : Prop :=
  z ∉ L.lattice ∧ ‖ι (L.weierstrassP z - r)‖ ≤ 1

theorem not_red_of_mem (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {z : ℂ} (h : z ∈ L.lattice) : ¬ Red ι L r z :=
  fun h' => h'.1 h

end GlobalTheory.Klein
