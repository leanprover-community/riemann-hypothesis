module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.exists_normal_frames_and_base_point_split_place : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  first | exact @GlobalTheory.LocMod.normalFrames_and_basePoint_exist | exact GlobalTheory.LocMod.normalFrames_and_basePoint_exist | (intros; apply GlobalTheory.LocMod.normalFrames_and_basePoint_exist <;> assumption)
