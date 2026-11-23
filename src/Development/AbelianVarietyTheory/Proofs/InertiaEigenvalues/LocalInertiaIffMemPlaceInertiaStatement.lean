module

public import Formalism.GaloisCohomology.StatementLoc
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertia
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.localInertia_iff_mem_placeInertia : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p)),
      (∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x)) →
      ∀ g : ↥(A.decompositionSubgroup F), i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  first | exact @GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | exact GlobalTheory.DecInertia.inertiaK_iff_mem_Ine | (intros; apply GlobalTheory.DecInertia.inertiaK_iff_mem_Ine <;> assumption)
