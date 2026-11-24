module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowers
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

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.dominant_monoid_elements_are_antitone_powers : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (s : GL (Fin n) L), s ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) → ∃ a : Fin n → ℤ, Antitone a ∧ s = GlobalTheory.CompanionTheory.CartGL.dPow p a := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | exact GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | (intros; apply GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone <;> assumption)
