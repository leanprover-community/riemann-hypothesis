module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.SquareIntegrableSegments.SegmentReordering.CsReorderord
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace CompanionTheory.PfEss.Zc2

section OrderFree

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrGL_eq_of_isLSeg_same {Δ : Segment k} {x y : IrrGL (k := k)} (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) :
    x = y := by
  obtain ⟨n, c⟩ := x
  obtain ⟨m, c'⟩ := y
  have hn : Δ.deg = n := hx.deg_eq
  have hm : Δ.deg = m := hy.deg_eq
  obtain rfl : n = m := hn.symm.trans hm
  rw [← IrrGL.of_rep ⟨n, c⟩, ← IrrGL.of_rep ⟨n, c'⟩]
  exact IrrGL.of_eq_of.2 (IsLSeg.unique hy hx)

theorem perm_of_univ_map_eq {α : Type*} {l : ℕ} {x y : Fin l → α}
    (h : Finset.univ.val.map y = Finset.univ.val.map x) : ∃ e : Equiv.Perm (Fin l), ∀ a, y a = x (e a) := by
  classical
  have hc : ∀ z, Fintype.card {a // y a = z} = Fintype.card {a // x a = z} := fun z => by
    have h1 := congrArg (Multiset.count z) h
    simp only [Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    simpa [Finset.card, Finset.filter, eq_comm] using h1
  exact ⟨Equiv.ofFiberEquiv (f := y) (g := x) fun z => Fintype.equivOfCardEq (hc z),
    fun a => (Equiv.ofFiberEquiv_map _ a).symm⟩

end OrderFree

theorem cs_orderfree : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LUnlinkedComm k → LOrderFree k := by
  intro k _ _ _ _ hA hcomm 𝔪 h N x hd hx V _ _ π hπ
  obtain ⟨h', y, hd', ⟨Γy, ⟨hmy, hordy⟩, hLy⟩, hcos⟩ := hπ
  obtain ⟨Γx, ⟨hmx, hordx⟩, hLx⟩ := hx

  have hcard : h' = h := by
    have := congrArg Multiset.card (hmy.trans hmx.symm)
    simpa using this
  subst hcard

  obtain ⟨σ, hσ⟩ := perm_of_univ_map_eq (hmy.trans hmx.symm)
  have hy : y = x ∘ σ := funext fun a => by
    have h1 : IsLSeg (Γx (σ a)) (y a).rep := hσ a ▸ hLy a
    exact irrGL_eq_of_isLSeg_same h1 (hLx (σ a))
  have hΓ : Γy = Γx ∘ σ := funext hσ
  subst hy
  subst hΓ
  obtain ⟨φ⟩ := cs_reorderord hA hcomm Γx σ x hd hd' hordx hordy hLx
  exact hcos.of_equiv (Representation.Equiv.refl _) φ.symm

end CompanionTheory.PfEss.Zc2
