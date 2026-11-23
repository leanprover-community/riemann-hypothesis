module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariant
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

open Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.exists_extension_rep_index_two_of_trace_invariant : ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k] [CharZero k] [IsAlgClosed k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ) (η : Γ →* ℤˣ), IsOpen (η.ker : Set Γ) → ∀ r : η.ker →* GL (Fin n) k, Continuous r → IsSSRep r → (∀ (g : Γ) (h h' : η.ker), (h' : Γ) = g * h * g⁻¹ → ((r h' : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → ∃ ρ : Γ →* GL (Fin n) k, Continuous ρ ∧ IsSSRep ρ ∧ ∀ h : η.ker, ρ h = r h := by
  first | exact @GlobalTheory.IndexTwoExt.main | exact GlobalTheory.IndexTwoExt.main | (intros; apply GlobalTheory.IndexTwoExt.main <;> assumption)
