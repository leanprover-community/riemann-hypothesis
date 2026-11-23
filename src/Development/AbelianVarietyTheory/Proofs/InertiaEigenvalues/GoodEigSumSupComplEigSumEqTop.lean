module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.Divisibility.ClassSum
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_good_sup_compl_eq_top : ∀ (D : D7) (i : D.nd.Loc), ZRat D (D.nd.mu i) (D.nd.j i) → SpecPr D i →
    D.nd.eigSum i ↑(D.nd.Zgood i) ⊔ D.nd.eigSum i (↑(D.nd.Zgood i))ᶜ = ⊤ := by
  intro D i hZ hS
  rw [eq_top_iff, ← D.nd.prMt_span i, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i)) ⊔
      ratSub D (D.nd.mu i) (D.nd.j i) (Idx.Z0 D (D.nd.mu i) (D.nd.j i))ᗮ := by
    unfold ZRat at hZ
    rw [hZ]; exact Submodule.mem_top
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hS.1 u hu) (hS.2 u' hu')

end GlobalTheory.EtaJoin
