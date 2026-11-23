module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneAdelicGLLocallyCompactDiscreteFiniteCovol
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

theorem _root_.GlobalTheory.T.normOneAdelicGL_locallyCompact_discrete_finiteCovolume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (k : ℕ), LocallyCompactSpace ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ SecondCountableTopology ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker ∧ DiscreteTopology ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) ∧ ∀ [MeasurableSpace (GL (Fin k) (AF F ⊗[F] E))] [BorelSpace (GL (Fin k) (AF F ⊗[F] E))] (π : Measure ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) (DM : Set ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker), π.IsHaarMeasure → IsFundamentalDomain ((bc (inclR (F := F) (AF F)) : GL (Fin k) E →* GL (Fin k) (AF F ⊗[F] E)).range.subgroupOf ((absE F E).comp (Matrix.GeneralLinearGroup.det : GL (Fin k) (AF F ⊗[F] E) →* (AF F ⊗[F] E)ˣ)).ker) DM π → π DM ≠ ⊤ := by
  first | exact @GlobalTheory.GLOneVol.glOne_finvol | exact GlobalTheory.GLOneVol.glOne_finvol | (intros; apply GlobalTheory.GLOneVol.glOne_finvol <;> assumption)
