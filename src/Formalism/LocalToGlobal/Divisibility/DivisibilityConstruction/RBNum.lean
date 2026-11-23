module

public import Formalism.LocalToGlobal.Divisibility.RecBridge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions

noncomputable section

namespace Formalism.L2.DIV.Cons

open Formalism.L2.DIV

variable {D : D7}

theorem rdTie (L : SizeData₂ D) (Del h0 : ℕ) : (ofRecord D L Del h0).rd = D.host.rdE := ofRecord_rd D L Del h0

theorem mainTie (L : SizeData₂ D) (Del h0 : ℕ) (u : D.what₂.Word) :
    (ofRecord D L Del h0).mainT (D.mem u).A.T = L.MAIN u := by
  simp only [NumDatum.mainT, SizeData₂.MAIN]
  rw [← Finset.sum_coe_sort D.host.TT]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [ofRecord_aT, ofRecord_logOm]
  first
  | rfl
  | (unfold Formalism.LatticeIndexTer.ph phF; ring)

theorem numRecTie_record (L : SizeData₂ D) (Del h0 : ℕ) (u : D.what₂.Word) :
    NumRecTie (ofRecord D L Del h0) L u ((D.mem u).A.T) L.Nc :=
  numRecTie_ofRecord L Del h0 u (rdTie L Del h0) (mainTie L Del h0 u)

end Formalism.L2.DIV.Cons

end
