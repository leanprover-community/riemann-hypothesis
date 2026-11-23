module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLatticesGoodPositionAllPlaces
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.exists_lattices_goodPosition_all_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → IsSelfDualC c.T v.NT → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : Lat c.Lz, IsSelfDualC _ LZ ∧ OrthAt (c.oT n h) (c.x n).L v.NT LZ x) → ∃ (N : ∀ j, Lat (c.V j)) (M : ∀ j ρ h, Lat (c.bes j ρ h).V₀) (β₀ : ∀ j ρ h i, Frame (o.p i) (c.bes j ρ h).V₀ (Fin (c.X j).rank ⊕ Fin 1)), (∀ j, j < D.R.m → IsSelfDualC (c.V j) (N j)) ∧ (∀ x, GoodAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ (∀ x, x ∉ v.tP → SplitAt { v with N := N } { o with M := M, β₀ := β₀ } x) ∧ ∀ j ρ h i, GluedCore (c.B j ρ h) (M j ρ h) o.q (o.β j i) (β₀ j ρ h i) (o.Q j i) := by
  first | exact @GlobalTheory.GoodPos.exists_goodAt | exact GlobalTheory.GoodPos.exists_goodAt | (intros; apply GlobalTheory.GoodPos.exists_goodAt <;> assumption)
