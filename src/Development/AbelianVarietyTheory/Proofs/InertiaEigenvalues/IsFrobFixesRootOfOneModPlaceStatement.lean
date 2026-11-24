module

public import Formalism.ConjugateSelfDual.Statement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFrobFixesRootOfOneModPlace
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.isFrob_fixes_root_of_one_mod_place : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (M : ℕ) (ζ : F),
    IsPrimitiveRoot ζ M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ →
    ∀ x : 𝓞 F, x - 1 ∈ v.asIdeal → ∀ w : Ω, w ^ M = algebraMap F Ω (x : F) → σ w = w := by
  first | exact @GlobalTheory.frob_fixes_root_of_one_mod | exact GlobalTheory.frob_fixes_root_of_one_mod | (intros; apply GlobalTheory.frob_fixes_root_of_one_mod <;> assumption)
