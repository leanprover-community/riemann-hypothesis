module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
public import GroundTheory.GlobalFields.TateThesis.EulerFactorsFinite
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HeckeGaussSumLocalTerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)


theorem _root_.GlobalTheory.T.hecke_gauss_sum_local_term : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (hu : IsUnitary χ) (v : HeightOneSpectrum (𝓞 E)) (m : ℕ), m ≠ 0 → ExpAt χ v m → ∑ᶠ r : 𝓞 E ⧸ v.asIdeal ^ m, (toHecke χ hu).finiteTest v (algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) * psiAt v (((atFin v (unif v ^ (m + diffExp v)) : (v.adicCompletion E)ˣ) : v.adicCompletion E)⁻¹ * algebraMap E (v.adicCompletion E) ((Quotient.out r : 𝓞 E) : E)) = gaussSumAt χ v m (unif v ^ (m + diffExp v)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | exact GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt | (intros; apply GlobalTheory.CompanionTheory.HeckeBridge.GaussSum.finiteTest_sum_eq_gaussSumAt <;> assumption)
