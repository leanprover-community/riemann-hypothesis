module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
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

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.ScalarUniq

theorem scalarBy_unique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (t : kˣ) (c c' : ℂ) (h : Zl.ScalarBy x t c) (h' : Zl.ScalarBy x t c') : c = c' := by
  have hirr : x.rep.IsIrreducible := x.2.rep.irr
  have hnt : Nontrivial x.2.rep.V := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    obtain ⟨a, b, hab⟩ := (hirr.toNontrivial : Nontrivial (Subrepresentation x.rep)).exists_pair_ne
    refine hab ?_
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have e : c • v = c' • v := (h v).symm.trans (h' v)
  exact smul_left_injective ℂ hv e

end GlobalTheory.CompanionTheory.ScalarUniq
