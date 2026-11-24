module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Blocks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modBlocks_some {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a : ℕ)
    (l : List (Bˣ × ℕ+)) (h : modBlocks f a bs = some l) :
    l.map (fun x => ((x.1 : B), (x.2 : ℕ))) = mapBlocks f a bs := by
  induction bs generalizing a l with
  | nil =>
    simp only [modBlocks, Option.some.injEq] at h
    subst h
    simp [mapBlocks]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
    simp [mapBlocks, ih (a + s) l' hl']

theorem mapBlocks_snd {A B : Type} (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a : ℕ) :
    (mapBlocks f a bs).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing a with
  | nil => simp [mapBlocks]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp [mapBlocks, ih]

theorem blkDet_append {K : Type} [CommRing K] (l1 l2 : List (K × ℕ)) :
    blkDet (l1 ++ l2) = blkDet l1 * blkDet l2 := by
  induction l1 with
  | nil => simp [blkDet]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.cons_append, blkDet, ih]
    ring

end PI.SupportDatumW
