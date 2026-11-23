module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.QuotientIsHausdorff
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ProperlyDiscontinuousFlags
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PropDiscCompare

open NumberField Topology ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}


open NumberField Topology in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.PropDiscCompare.compact_of_local (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (h : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ProperlyDiscontinuousFlags.ProperlyDiscontinuousOnFlags X := by
  intro K hK hKdom
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PropDisc at h
  choose! U hU U' hU' hfin using h
  obtain ⟨t, ht, hcover⟩ := (hK.prod hK).elim_nhds_subcover
    (fun q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r × _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => U q.1 q.2 ×ˢ U' q.1 q.2)
    (fun q hq => prod_mem_nhds (hU q.1 (hKdom hq.1) q.2 (hKdom hq.2))
      (hU' q.1 (hKdom hq.1) q.2 (hKdom hq.2)))
  refine (t.finite_toSet.biUnion fun q hq =>
    hfin q.1 (hKdom (ht q hq).1) q.2 (hKdom (ht q hq).2)).subset ?_
  rintro γ ⟨hγ, x, hx, y, hy, b, hb, hxy⟩
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp (hcover (Set.mk_mem_prod hx hy))
  exact Set.mem_iUnion₂.mpr ⟨q, hq, hγ, x, hxq.1, y, hxq.2, b, hb, hxy⟩

end GlobalTheory.PropDiscCompare
