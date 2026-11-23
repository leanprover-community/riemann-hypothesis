module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassOnFinerEtaleNbhdCurve
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

theorem _root_.GlobalTheory.T.exists_kummerClass_on_finer_etaleNbhd_curve : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ (A₂ : Type) (_ : CommRing A₂) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂), IsExcisionNbhd B A₂ f ∧ ∃ c : (Γ(Spec (CommRingCat.of (Localization.Away (algebraMap B A₂ f))), ⊤))ˣ, ∀ φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → pull _ (spMap φ) _ _ w = kum q c := by
  first | (exact @GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (exact GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd) | (intros; apply GlobalTheory.EtC.KummerLoc.exists_kummer_on_finer_nbhd <;> assumption)
