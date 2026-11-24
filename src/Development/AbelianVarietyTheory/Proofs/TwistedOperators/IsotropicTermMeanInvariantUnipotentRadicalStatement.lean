module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicTermMeanInvariantUnipotentRadical
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isotropicTermMean_invariant_unipotentRadical : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (κ : Measure (NI V C)) (𝓝 : Set (NI V C)), κ.IsHaarMeasure → IsFundamentalDomain (NIQ V C) 𝓝 κ → ∀ (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E) (m : Matrix (Fin s) (Fin r) D.host.E), IsIsoFrame W L → m.rank = s → ∀ (n' : NI W L) f, IsThetaFunO ψ V W f → ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), (n' : GA D W)) f)) 0 ∂κ = ∫ n in 𝓝, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map (L * m) (incA D))) (ω ((n : GA D V), 1) f)) 0 ∂κ := by
  first | exact @GlobalTheory.IsoTermMean.mean_isoTerm_invariant | exact GlobalTheory.IsoTermMean.mean_isoTerm_invariant | (intros; apply GlobalTheory.IsoTermMean.mean_isoTerm_invariant <;> assumption)
