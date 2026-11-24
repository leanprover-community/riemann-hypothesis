module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalMeanEqVolumeMulRationalMean
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotentRadicalMean_eq_volume_mul_rationalMean : ∀ (D : D7) (V V' : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (m : Matrix (Fin s) (Fin r) D.host.E), m.rank = s → ∃ (μ : Measure (Mx D s V'.rank)) (𝓐 : Set (Mx D s V'.rank)), IsCovolOne (ratMx D s V'.rank) μ 𝓐 ∧ ∀ φ : Mx D s V'.rank → ℂ, Continuous φ → (∀ γ ∈ ratMx D s V'.rank, ∀ a, φ (γ + a) = φ a) → ∫ n in 𝓝, φ (HMul.hMul (HMul.hMul ((m * adj D C' * V.gram).map (incA D) : Matrix (Fin s) (Fin V.rank) (AE D)) (mt V (n : GA D V) - 1)) (B.map (incA D) : Matrix (Fin V.rank) (Fin V'.rank) (AE D))) ∂κ = ((κ 𝓝).toReal : ℂ) * ∫ a in 𝓐, φ a ∂μ := by
  first | exact @GlobalTheory.UnipMean.mean_eq_volume_mul | exact GlobalTheory.UnipMean.mean_eq_volume_mul | (intros; apply GlobalTheory.UnipMean.mean_eq_volume_mul <;> assumption)
