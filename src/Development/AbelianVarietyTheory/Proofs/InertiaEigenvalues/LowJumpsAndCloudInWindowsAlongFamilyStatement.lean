module

public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LowJumpsAndCloudInWindowsAlongFamily
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.lowJumps_and_cloud_in_windows_along_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ), Fm.x1 < x → ∀ (a : Fm.Ix x) (j : ℕ), 1 ≤ j → j ≤ (Fm.D x a).R.m →
    ∀ (up : Bool) (ρ : (Fm.D x a).what₂.Tau),
    (∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.lowT (Fm.D x a) up j ρ →
      |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2| ≤ (Fm.L x a).etaSz ∧
      2 * ((Fm.L x a).sc.b / LevelStarExponents.lStar (Fm.L x a)) + ((Fm.D x a).R.t : ℝ) / 2 + 3 ≤
        |(z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2|) ∧
    ∃ W0 ∈ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.baseSizes (Fm.L x a), ∀ z : ℤ, (z : ℚ) ∈ AdmissibleParameterJ.cloudT (Fm.D x a) up j ρ →
      W0 ≤ (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - (((Fm.D x a).R.t : ℝ) - 1) / 2 else (((Fm.D x a).R.t : ℝ) - 1) / 2 - z) ≤
        W0 + (Fm.L x a).Sc + (Fm.L x a).etaSz + 1 := by
  first | exact @GlobalTheory.LetterWindows.lows_cloud_windows | exact GlobalTheory.LetterWindows.lows_cloud_windows | (intros; apply GlobalTheory.LetterWindows.lows_cloud_windows <;> assumption)
