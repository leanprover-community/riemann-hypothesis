module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagFieldChange
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

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.generic_flag_field_change : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (S : Type) (r : S → ℕ) (d : ℕ), 0 < d → (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : GenIx r => algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X q))) (GenField Ω r) = d) → ∀ (E₀ E' : Type) [AddCommGroup E₀] [Module Ω₀ E₀] [AddCommGroup E'] [Module (GenField Ω r) E'] (j : E₀ →+ E') (V₀ : S → Submodule Ω₀ E₀) (c : ∀ s, Fin (r s) → E₀), (∀ s, LinearIndependent Ω₀ (c s) ∧ Submodule.span Ω₀ (Set.range (c s)) = V₀ s) → (∀ (a : Ω₀) e, j (a • e) = algebraMap Ω (GenField Ω r) (fn a) • j e) → (∀ s, LinearIndependent (GenField Ω r) fun k => j (c s k)) → (∀ s, Submodule.span (GenField Ω r) (Set.range fun k => ∑ l, genU Ω r s l k • j (c s l)) = Submodule.span (GenField Ω r) (Set.range fun k => j (c s k))) ∧ (letI := ((algebraMap Ω (GenField Ω r)).comp fn).toAlgebra; IsGenericFlag (Ω' := GenField Ω r) j V₀ (fun s k => ∑ l, genU Ω r s l k • j (c s l)) d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | exact GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.GenericColumns.isGenericFlag_columns <;> assumption)
