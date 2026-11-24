module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegIncDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_equiv_prodIrr_of_cast {h h' N : ℕ} (e : h = h') (x : Fin h → IrrGL (k := k)) (y : Fin h' → IrrGL (k := k))
    (hxy : ∀ a, x a = y (Fin.cast e a)) (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr y hd')) := by
  subst e
  obtain rfl : x = y := funext fun a => by simpa using hxy a
  exact ⟨hd, ⟨Representation.Equiv.refl _⟩⟩

theorem nonempty_contra_trans {h h' N : ℕ} {x y : Fin h → IrrGL (k := k)} {z : Fin h' → IrrGL (k := k)} {hd : ∑ a, (x a).1 = N}
    {hy : ∑ a, (y a).1 = N} {hz : ∑ a, (z a).1 = N} (H₁ : Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hy)))
    (H₂ : Nonempty ((prodIrr y hy).Equiv (prodIrr z hz))) :
    Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr z hz)) :=
  H₁.elim fun φ => H₂.elim fun ψ => ⟨φ.trans ψ⟩

theorem dualCl_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (hl : Δ.len = (segDual Δ).len)
    (a : Fin Δ.len) : dualCl (Δ.term a) = dec (segDual Δ) (Fin.cast hl a) := by
  have hc : ∀ x : IrrGL (k := k), x.IsCusp → (dualCl x).IsCusp := fun x hx =>
    (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  have hv : ((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) = Δ.len - (a + 1) := by
    have h0 : ((Fin.cast hl a : Fin (segDual Δ).len) : ℕ) = a := rfl
    rw [Fin.val_rev, h0]; omega
  have ha : (a : ℕ) + 1 ≤ Δ.len := a.2
  change dualCl (Δ.first.nu ((a : ℕ) : ℂ)) =
    (segDual Δ).first.nu (((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) : ℂ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, IrrGL.nu_nu, hv, Nat.cast_sub ha]
  congr 1
  push_cast
  ring

theorem contra_prodIrr_term : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N,
      Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  intro k _ _ _ _ hA Δ N hd
  have hl : Δ.len = (segDual Δ).len :=
    (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual (fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1) Δ).symm
  have H := @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr k _ _ _ _ hA Δ.len N Δ.term hd
  obtain ⟨hd₁, H₁⟩ := H
  have H' := exists_equiv_prodIrr_of_cast hl (fun a => dualCl (Δ.term a)) (dec (segDual Δ))
    (dualCl_term hA Δ hl) hd₁
  obtain ⟨hd₂, H₂⟩ := H'
  exact ⟨hd₂, nonempty_contra_trans H₁ H₂⟩

end GlobalTheory.CompanionTheory.SegIncDual

end
