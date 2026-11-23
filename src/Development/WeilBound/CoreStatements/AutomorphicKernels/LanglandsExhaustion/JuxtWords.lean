module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.JuxtWords
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.JuxtDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjectiveStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem decW_up (Δ : Segment k) : decW (up Δ) = nxt Δ :: decW Δ := by
  apply CompanionTheory.Exh.decW_up <;> assumption

theorem nxt_not_mem (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) : nxt Δ ∉ decW Δ := by
  intro h
  rw [decW, List.mem_ofFn] at h
  obtain ⟨i, hi⟩ := h
  have h2 := GlobalTheory.T.cuspidal_twist_injective hA Δ.first Δ.isCusp_first _ _ hi
  have h3 := (Fin.rev i).isLt
  omega

theorem eq_decW_of_append (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (u P Q : List (IrrGL (k := k)))
    (h1 : decW Δ = P ++ Q) (h2 : u ++ [nxt Δ] = P ++ nxt Δ :: Q) : u = decW Δ := by
  apply CompanionTheory.Exh.eq_decW_of_append <;> assumption

end PositivityTheory.Exh

end
