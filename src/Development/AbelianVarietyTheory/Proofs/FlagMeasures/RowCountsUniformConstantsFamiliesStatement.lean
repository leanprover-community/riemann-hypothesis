module

public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowCountsUniformConstantsFamilies
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

theorem _root_.GlobalTheory.T.rowCounts_uniform_constants_families : Formalism.HermitianLatticesTheory.SiegelMassRatio → ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ c3 cH cS c4 thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → (∀ C ≥ c3, (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm20 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A 3 C)) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.HerrCocycleExtensionClass (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cH) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.ArchimedeanSignatureMatching (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A cS) ∧ (OwnEv Fm fun C' Cl x i => ∀ u u', VanishingOnXAndXPlus.adm21 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A c4) := by
  first | exact @GlobalTheory.RowCounts.uniform_counts | exact GlobalTheory.RowCounts.uniform_counts | (intros; apply GlobalTheory.RowCounts.uniform_counts <;> assumption)
