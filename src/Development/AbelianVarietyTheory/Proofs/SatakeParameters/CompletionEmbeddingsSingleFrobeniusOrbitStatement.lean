module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletionEmbeddingsSingleFrobeniusOrbit
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem _root_.GlobalTheory.T.completion_embeddings_single_frobenius_orbit : ∀ {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime], l ∉ H.small → l ≠ H.q → l ≠ H.d → ∀ (c : H.E →+* PadicAlgCl l) (K : Loc.FinExt l) (hc : ∀ x, c x ∈ K.1), (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(l : ℤ)})] (s : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ s P → Module.finrank ℚ_[l] ↥K.1 = orderOf (H.galE s) ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l, ∃! i : ZMod (orderOf (H.galE s)), ∀ x : H.E, τ ⟨c x, hc x⟩ = c ((s ^ i.val) x) := by
  first | exact @GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | exact GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit | (intros; apply GlobalTheory.LocalFrobeniusOrbit.embeddings_orbit <;> assumption)
