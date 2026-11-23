module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
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
import Mathlib.Tactic.Linter.HaveILetI
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

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.Jacquet

theorem finiteDimensional_fixed_jac :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
      (hd : ∑ _a : Fin n, 1 = n) {V : Type} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin n) k) V), IsAdmissible π → PositivityTheory.Lbc.C0 k → PositivityTheory.Lbc.C3 k →
      ∀ m, 1 ≤ m → FiniteDimensional ℂ ↥(fixed (jac (stdBlocks (fun _ : Fin n => 1) hd) π)
        (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd)) := by
  intro k _ _ _ _ n hd V _ _ π hπ h0 h3 m hm
  obtain ⟨hopen, hcompact, hfact⟩ := h0 n m n (fun _ : Fin n => 1) hd hm
  obtain ⟨-, hsurj, -⟩ := h3 n n (fun _ : Fin n => 1) hd (Zls.Km k n m) hopen hcompact hfact
    (fun _ => Nat.one_pos) V π hπ
  haveI : FiniteDimensional ℂ ↥(fixed π (Zls.Km k n m)) := hπ.2 _ hopen hcompact
  let f : ↥(fixed π (Zls.Km k n m)) →ₗ[ℂ]
      Jacquet π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) :=
    (Submodule.mkQ _).comp (Submodule.subtype _)
  have hle : fixed (jac (stdBlocks (fun _ : Fin n => 1) hd) π)
      (PositivityTheory.Lbc.KM k n (Zls.Km k n m) (fun _ : Fin n => 1) hd) ≤ LinearMap.range f := by
    intro w hw
    obtain ⟨v, hv⟩ := hsurj w hw
    exact ⟨v, hv⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.CompanionTheory.Jacquet
