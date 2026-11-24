module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.BlowupAmpleRelative
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.blowup_ample_relative : ∀ (k : Type) [Field k] [CharZero k] (Y₀ Y₁ : Scheme.{0}) [IsIntegral Y₀] [IsIntegral Y₁] [IsLocallyNoetherian Y₀] [IsLocallyNoetherian Y₁] (q : Y₀ ⟶ Sp k) (n : ℕ) (t : Y₁ ⟶ Y₀) [IsDominant t] [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension n (t ≫ q)], IsProjOver q → IsProjOver (t ≫ q) → ∀ I : Y₀.IdealSheafData, IsIso (t ∣_ I.support.compl) → FinalTheorems.EffCartier (I.comap t) → ∀ (A : LB Y₀) (hA : IsAmpleLB A), ∃ (c : ℕ) (E : CartierDiv Y₁) (A₁ : LB Y₁) (hA₁ : IsAmpleLB A₁), 0 < c ∧ E.Eff ∧ E.supp ≤ (I.comap t).support ∧ c • CechPic.pull t (cls A hA.isLB) = cls A₁ hA₁.isLB + toPic E := by
  first | exact @_root_.GlobalTheory.exists_ample_pull_sub_eff | exact _root_.GlobalTheory.exists_ample_pull_sub_eff | (intros; apply _root_.GlobalTheory.exists_ample_pull_sub_eff <;> assumption)
