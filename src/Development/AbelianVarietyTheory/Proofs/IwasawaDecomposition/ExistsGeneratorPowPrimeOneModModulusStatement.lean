module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratorPowPrimeOneModModulus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

theorem _root_.GlobalTheory.T.exists_generator_pow_prime_one_mod_modulus : ∀ (L : Type) [Field L] [NumberField L] (𝔮 : Ideal (𝓞 L)) (h : ℕ), 𝔮 ≠ ⊥ → (∀ I : Ideal (𝓞 L), I ≠ ⊥ → IsCoprime I 𝔮 → ∃ α β : 𝓞 L, RayPair 𝔮 α β ∧ I ^ h * Ideal.span {β} = Ideal.span {α}) → ∀ v : HeightOneSpectrum (𝓞 L), ∃ k : Lˣ, FractionalIdeal.spanSingleton (𝓞 L)⁰ (k : L) = (v.asIdeal : FractionalIdeal (𝓞 L)⁰ L) ^ h ∧ ∀ w : HeightOneSpectrum (𝓞 L), w ≠ v → w.asIdeal ∣ 𝔮 → w.valuation L ((k : L) - 1) < 1 := by
  exact @GlobalTheory.Mem.FieldsEx.exists_gen_pow_prime_one_mod
