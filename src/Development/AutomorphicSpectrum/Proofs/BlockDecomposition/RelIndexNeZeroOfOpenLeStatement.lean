module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.Group.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexNeZeroOfOpenLe
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf

@[expose] public section

open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

theorem _root_.GlobalTheory.T.rel_index_ne_zero_of_open_le : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (K L : Subgroup H), IsOpen (L : Set H) → IsCompact (K : Set H) → L ≤ K → L.relIndex K ≠ 0 ∧ ∀ (T C : Subgroup H) (x : H), (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 → (T ⊓ L.map (MulAut.conj x).toMonoidHom).relIndex C ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | exact GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted | (intros; apply GlobalTheory.CompanionTheory.OrbitalCount.relIndex_open_compact_and_twisted <;> assumption)
