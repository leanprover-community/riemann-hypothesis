module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

theorem _root_.GlobalTheory.T.exists_archimedean_lift_unitaryGroupProduct : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∃ L : (D.what₂.Tau → Mt V.rank) → GA D V, (∀ u ∈ UG (gramAt D V), L u ∈ GinfC V ∧ ∀ τ, archM V (θ τ) (L u) = u τ) ∧ (∀ u ∈ UG (gramAt D V), ∀ u' ∈ UG (gramAt D V), L (u * u') = L u * L u') ∧ ContinuousOn L (UG (gramAt D V)) ∧ (∀ g, (fun τ => archM V (θ τ) g) ∈ UG (gramAt D V)) ∧ (∀ u ∈ GinfC V, L (fun τ => archM V (θ τ) u) = u) ∧ (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), atTau θ V τ g = L (Pi.mulSingle τ g)) ∧ (∀ g, ∃ a ∈ GfC V, ∃ u ∈ GinfC V, g = a * u) ∧ (∀ a ∈ GfC V, ∀ u ∈ GinfC V, a * u = u * a) ∧ ∀ τ, (gramAt D V τ).IsHermitian ∧ (gramAt D V τ).det ≠ 0 := by
  first | exact @GlobalTheory.RealLift.exists_real_lift | exact GlobalTheory.RealLift.exists_real_lift | (intros; apply GlobalTheory.RealLift.exists_real_lift <;> assumption)
