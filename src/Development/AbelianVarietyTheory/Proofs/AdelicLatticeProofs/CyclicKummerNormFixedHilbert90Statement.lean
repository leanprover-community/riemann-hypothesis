module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90
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

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff : ∀ (p : ℕ) (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → FiniteDimensional F E ∧ Module.finrank F E = p ∧ (∀ y : E, σ^[p] y = y) ∧ (∀ y : E, σ y = y → ∃ a : F, y = algebraMap F E a) ∧ (∀ y : E, ∏ i ∈ Finset.range p, σ^[i] y = 1 → ∃ z : E, z ≠ 0 ∧ y = σ z / z) ∧ (∀ (u : F) (y : E), y ^ p = algebraMap F E u → ∃ (k : ℕ) (r : F), u = δ ^ k * r ^ p) ∧ ∀ x : Fˣ, x ∈ kNorm p (RingHom.id F) δ ↔ ∃ y : E, ∏ i ∈ Finset.range p, σ^[i] y = algebraMap F E (x : F) := by
  first | exact @GlobalTheory.CNorm.kummer_basic | exact GlobalTheory.CNorm.kummer_basic | (intros; apply GlobalTheory.CNorm.kummer_basic <;> assumption)
