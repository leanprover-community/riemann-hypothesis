module

import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThickeningGroupHomExtends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.EqRed
open GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]

theorem eq_zero_of_forall_mem_map (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (x : A)
    (h : ∀ e : ℕ, x ∈ (I ^ (e + 1)).map (algebraMap R A)) : x = 0 := by
  have hI : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have key := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := A) I
    (by simpa only [Ideal.jacobson_bot] using hI)
  have hx : x ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule R A)) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    have h1 : x ∈ (I ^ (i + 1) • (⊤ : Submodule R A)) := by
      rw [Ideal.smul_top_eq_map]
      exact h i
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ i)) h1
  rw [key] at hx
  simpa using hx

theorem eq_of_reductions (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y)
    (h : ∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) : f = g := by
  apply (config := { allowSynthFailures := true }) GlobalTheory.CompanionTheory.Ar.BT.LiftHom.hom_ext_of_finite <;> assumption

end GlobalTheory.CompanionTheory.Ar.BT.EqRed
