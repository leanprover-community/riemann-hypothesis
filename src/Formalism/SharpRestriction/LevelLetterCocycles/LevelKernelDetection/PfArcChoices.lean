module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
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

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.MainNotions.WachCoordinates

theorem hn_of {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hCu : CutsOK n j ty cuts arcLen) {c : ZMod n} (hc : c ∈ (cutsOf hCu).cuts) :
    (cutsOf hCu).ell c ≤ n :=
  (cutsOf hCu).ell_le c hc

theorem hj_of {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hCu : CutsOK n j ty cuts arcLen) {c : ZMod n} (hc : c ∈ (cutsOf hCu).cuts) :
    j ≤ (cutsOf hCu).ell c := by
  simp only [Formalism.MainNotions.WachCoordinates.cutsOf_cuts] at hc
  simp only [Formalism.MainNotions.WachCoordinates.cutsOf_ell]
  exact hCu.2.2.2.1 c hc

theorem three_g_le_parameter_bound {l : ℕ} (hl : 2 ≤ l) {G S η h : ℕ} (hg : gPar G S η ≤ h) :
    3 * gPar G S η ≤ (l - 1) * Formalism.ExponentWindows.E.parM l h (gPar G S η) := by
  unfold Formalism.ExponentWindows.E.parM
  have hd : 0 < l - 1 := by omega
  have h1 := Nat.lt_mul_div_succ (h + 2 * gPar G S η) hd
  exact le_of_lt (lt_of_le_of_lt (by omega) h1)

end Formalism.MainNotions.N.Ln03.Pf
