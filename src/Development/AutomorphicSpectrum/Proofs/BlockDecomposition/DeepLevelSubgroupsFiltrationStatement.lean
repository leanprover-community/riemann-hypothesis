module

public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltration
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.deep_level_subgroups_filtration : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (hd : ∑ _a : Fin n, 1 = n), Antitone (fun m => PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd) ∧ ∀ m m', m ≤ m' → ∀ u ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m + 1)) (fun _ : Fin n => 1) hd, ∃ N : ℕ, 0 < N ∧ u ^ N ∈ PositivityTheory.Lbc.KM k n (Zls.Km k n (m' + 1)) (fun _ : Fin n => 1) hd := by
  first | exact @GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow | exact GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow | (intros; apply GlobalTheory.CompanionTheory.KmPow.KM_antitone_and_pow <;> assumption)
