module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_up (Δ : Segment k) : decW (up Δ) = nxt Δ :: decW Δ := by
  show List.ofFn (fun i : Fin (Δ.len + 1) => (up Δ).term (Fin.rev i)) = _
  rw [List.ofFn_succ]
  congr 1
  simp only [decW]
  congr 1
  funext i
  show Δ.first.nu (((Fin.rev i.succ : Fin (Δ.len + 1)) : ℕ) : ℂ) = Δ.first.nu (((Fin.rev i : Fin Δ.len) : ℕ) : ℂ)
  have h : ((Fin.rev i.succ : Fin (Δ.len + 1)) : ℕ) = ((Fin.rev i : Fin Δ.len) : ℕ) := by
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  rw [h]

theorem nxt_not_mem (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : nxt Δ ∉ decW Δ := by
  intro h
  rw [decW, List.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  have h2 := _root_.GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj hA Δ.first Δ.isCusp_first _ _ hi
  omega

theorem eq_decW_of_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (u P Q : List (IrrGL (k := k)))
    (h1 : decW Δ = P ++ Q) (h2 : u ++ [nxt Δ] = P ++ nxt Δ :: Q) : u = decW Δ := by
  rcases Q.eq_nil_or_concat' with rfl | ⟨Q', q, rfl⟩
  · rw [h1, List.append_nil]
    exact (List.append_inj' h2 rfl).1
  · exfalso
    have h3 : u ++ [nxt Δ] = (P ++ nxt Δ :: Q') ++ [q] := by simpa using h2
    have h4 := (List.append_inj' h3 rfl).2
    have hq : q = nxt Δ := by simpa using h4.symm
    apply nxt_not_mem hA Δ
    rw [h1, ← hq]
    simp

end CompanionTheory.Exh

end
