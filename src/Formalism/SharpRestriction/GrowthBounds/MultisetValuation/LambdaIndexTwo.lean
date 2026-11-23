module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
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

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem lambda_index_one (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 1 = G.P.lam0 v s ⟨0, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨le_rfl, by omega⟩]

theorem lambda_index_two (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) : lamI (G.P.lam0 v) s 2 = G.P.lam0 v s ⟨1, by omega⟩ := by
  unfold lamI; rw [dite_eq_left ⟨by omega, by omega⟩]

theorem nc_w_ge (s : Fin (G.P.n' v)) (j : ℕ) (hj : 1 ≤ j) : Fl.w v 1 s ≤ Fl.w v j s := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ l hl ih => exact le_trans ih (Fl.w_mono v s l hl)

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
