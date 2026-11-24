module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselian
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.subsingleton_etaleCohomology_genericFibre_henselianLine : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  first | (exact @GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton) | (exact GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton) | (intros; apply GlobalTheory.EtC.GenFibreLine.genericFibre_subsingleton  <;> assumption)
