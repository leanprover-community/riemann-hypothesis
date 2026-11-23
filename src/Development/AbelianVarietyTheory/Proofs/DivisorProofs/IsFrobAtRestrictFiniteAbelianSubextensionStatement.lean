module

public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import ReciprocityTheory.NeutralLocalFields.Reciprocity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextension
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors

theorem _root_.GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal → haveI := h.finiteDimensional; haveI := h.isGalois; IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) Q := by
  first | exact @GlobalTheory.FrobRestrict.isFrobAt_restrict | exact GlobalTheory.FrobRestrict.isFrobAt_restrict | (intros; apply GlobalTheory.FrobRestrict.isFrobAt_restrict <;> assumption)
