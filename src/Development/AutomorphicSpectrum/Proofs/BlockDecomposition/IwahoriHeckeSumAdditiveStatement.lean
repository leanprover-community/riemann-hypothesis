module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriHeckeSumAdditive
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

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.iwahori_hecke_sum_additive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (ϖ : (w.adicCompletion E)ˣ), ordL (ϖ : w.adicCompletion E) = 1 → ∀ (x x' : Fin a → ℤ), Antitone x → Antitone x' → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GLw a w) V) (v : V), (∀ k ∈ iwGL a w, π k v = v) → ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ (x + x')) q.out • π q.out v = ∑ᶠ q : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x) q.out • π q.out (∑ᶠ q' : GLw a w ⧸ iwGL a w, dcos a w (tdiag ϖ x') q'.out • π q'.out v) := by
  first | exact @GlobalTheory.CompanionTheory.IwHeckeMul.main | exact GlobalTheory.CompanionTheory.IwHeckeMul.main | (intros; apply GlobalTheory.CompanionTheory.IwHeckeMul.main <;> assumption)
