module

public import Formalism.CharacterColumnKernels.Statement
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInvariantsOfScalarNeOneTwist
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
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  first | exact @GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | exact GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | (intros; apply GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one <;> assumption)
