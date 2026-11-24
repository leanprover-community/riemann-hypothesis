module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
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


theorem _root_.GlobalTheory.T.kummer_cocycle_norm_criterion : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N, (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ, (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) → ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) → (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) → ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω, c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | exact GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | (intros; apply GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary <;> assumption)
