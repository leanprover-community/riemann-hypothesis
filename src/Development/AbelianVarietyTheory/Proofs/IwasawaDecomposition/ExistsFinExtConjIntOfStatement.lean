module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinExtConjIntOf
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_finExt_conj_entries_mem_intOf : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] (a : ℕ) (ρ : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous (fun g => ((ρ g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l))) → ∃ (L : Loc.FinExt l) (P : GL (Fin a) (PadicAlgCl l)), ∀ g i k, ((P⁻¹ * ρ g * P : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i k ∈ Formalism.L2.TwC.intOf l L.1 := by
  first | exact @GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | exact GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf | (intros; apply GlobalTheory.IntegralConjFinExt.exists_finExt_conj_intOf <;> assumption)
