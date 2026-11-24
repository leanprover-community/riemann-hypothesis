module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCentralizerCompactPart
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

theorem _root_.GlobalTheory.T.twisted_centralizer_compact_part : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (θ : G →* G), Continuous θ → ∀ (K I C : Subgroup G) (δ : G), IsCompact (K : Set G) → IsOpen (I : Set G) → IsCompact (C : Set G) → cptPart (twCent θ δ) = twCent θ δ ⊓ C → ∀ x : G, twCent θ δ ⊓ K.map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent θ δ) ∧ (twCent θ δ ⊓ I.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ δ)) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.CentOk.centraliser_hyps | exact GlobalTheory.CompanionTheory.CentOk.centraliser_hyps | (intros; apply GlobalTheory.CompanionTheory.CentOk.centraliser_hyps <;> assumption)
