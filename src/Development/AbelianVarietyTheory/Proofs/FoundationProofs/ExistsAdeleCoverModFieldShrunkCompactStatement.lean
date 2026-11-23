module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValHalfInf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdeleCoverModFieldShrunkCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.Eis.Conv

theorem _root_.GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ (Ω : Set (AF F)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F), (Y.card : ℝ) ≤ C * ((2 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ a : AF F, ∃ x : F, ∃ y ∈ Y, ∃ ω ∈ Ω, a = algebraMap F (AF F) x + y + (halfInf F).1 ^ m * ω := by
  first | exact @GlobalTheory.Eis.ConvCover.exists_cover | exact GlobalTheory.Eis.ConvCover.exists_cover | (intros; apply GlobalTheory.Eis.ConvCover.exists_cover <;> assumption)
