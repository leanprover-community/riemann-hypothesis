module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowCalculus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

@[expose] public section

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem _root_.GlobalTheory.T.isLogDerivQExpansionModPrimePow_calculus : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f g : X.K) (φ ψ : HahnSeries ℚ Ω), (IsDl X A l n s f φ → IsDl X A l n s g ψ → IsDl X A l n s (f * g) (φ + ψ)) ∧ (IsDl X A l n s f φ → IsDl X A l n s f⁻¹ (-φ)) ∧ (IsDl X A l n s f φ → (∀ r, ψ.coeff r ∈ A) → (∀ r, CgA A l n (φ.coeff r) (ψ.coeff r)) → IsDl X A l n s f ψ) ∧ (∀ κ : Ω, κ ≠ 0 → IsDl X A l n s (algebraMap Ω X.K κ) 0) ∧ (∀ n', n' ≤ n → IsDl X A l n s f φ → IsDl X A l n' s f φ) := by
  first | exact @GlobalTheory.Glue.isDl_calc | exact GlobalTheory.Glue.isDl_calc | (intros; apply GlobalTheory.Glue.isDl_calc <;> assumption)
