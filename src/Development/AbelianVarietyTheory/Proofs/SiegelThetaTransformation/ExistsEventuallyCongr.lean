module

public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Mathlib.RingTheory.Finiteness.Defs
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Mathlib.Order.Filter.Ultrafilter.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetIndepStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory

namespace GlobalTheory.IsoTower

theorem finite_quot_nsmul (M : Type) [AddCommGroup M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    Finite (M ⧸ (nsmulAddMonoidHom n : M →+ M).range) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨y, rfl⟩

theorem exists_eventually_congr {L M : Type} [AddCommGroup L] [AddCommGroup M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (U : Ultrafilter ℕ) (g : ℕ → L →+ M) {n : ℕ} (hn : 0 < n)
    (P : ℕ → Prop) (hP : ∀ᶠ j in U, P j) :
    ∃ i, P i ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e := by
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 (inferInstance : Module.Finite ℤ L))
  have := hSf.to_subtype
  have := finite_quot_nsmul M hn
  let φ : ℕ → S → M ⧸ (nsmulAddMonoidHom n : M →+ M).range := fun j s => QuotientAddGroup.mk (g j s)
  obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map φ)
  have hv' : ∀ᶠ j in U, φ j = v := by
    have : {v} ∈ U.map φ := by
      rw [hv]
      exact rfl
    exact this
  obtain ⟨i, hi, hPi⟩ := (hv'.and hP).exists
  refine ⟨i, hPi, hv'.mono fun j hj a => ?_⟩
  have h := AddMonoidHom.eq_of_eqOn_dense hS
    (f := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g i))
    (g := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g j))
    (fun s hs => congrFun (hi.trans hj.symm) ⟨s, hs⟩)
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (DFunLike.congr_fun h a)
  refine ⟨e, ?_⟩
  have he' : n • e = -g i a + g j a := he
  rw [he']
  abel

end GlobalTheory.IsoTower
