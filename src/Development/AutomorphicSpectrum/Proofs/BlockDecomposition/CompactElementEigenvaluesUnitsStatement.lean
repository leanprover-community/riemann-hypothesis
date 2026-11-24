module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.compact_element_eigenvalues_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n : ℕ) (H : Subgroup (GLw n w)) (g : H) (p : GLw n w) (s : Fin n → (w.adicCompletion E)ˣ), g.1 = p * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) s * p⁻¹ → IsCompact (closure (Subgroup.zpowers g : Set H)) → ∀ i, Valued.v (s i : w.adicCompletion E) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | exact GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers | (intros; apply GlobalTheory.CompanionTheory.DiagBd.valued_eq_one_of_isCompact_closure_zpowers <;> assumption)
