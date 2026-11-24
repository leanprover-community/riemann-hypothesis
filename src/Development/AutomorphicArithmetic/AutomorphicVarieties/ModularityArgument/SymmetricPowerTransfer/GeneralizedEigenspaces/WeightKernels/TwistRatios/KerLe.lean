module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SubalgebraEqTop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Ga.kerLe :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (H : Type) [Group H] (n : ℕ) (R : H →* GL (Fin n) k), IsIrr R → ∀ (x₀ : GL (Fin n) k) (B : Type) [Ring B] [Algebra k B] [Module.Finite k B] (φ : H →* B) (f : B →ₗ[k] k), (∀ h, Ga.tr (x₀ * R h) = f (φ h)) → n ^ 2 ≤ Module.finrank k (Algebra.adjoin k (Set.range φ)) ∧ ∀ x : MonoidAlgebra k H, MonoidAlgebra.lift k B H φ x = 0 → MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) H ((Units.coeHom _).comp R) x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe26.kerLe
