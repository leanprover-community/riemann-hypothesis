module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem torsion_section_const : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (k : ℕ) (y : Out.baseOver (Sp (DualNumber ℂ)) ⟶ A') (y₀ : Out.baseOver (Sp ℂ) ⟶ P₀.A), k ≠ 0 → y ^ k = 1 → y₀ ^ k = 1 → (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ y.left = y₀.left ≫ j → y.left ≫ ρ = (spMap (algebraMap ℂ (DualNumber ℂ))) ≫ y₀.left := by
  intro _ P₀ A' _ ρ j hc k y y₀ hk hy hy₀ hyj
  letI := P₀.isAb.comm
  have hu : IsUnit ((k : ℕ) : Γ(Sp ℂ, ⊤)) := by
    let e : Γ(Sp ℂ, ⊤) ≃+* ℂ := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    refine (MulEquiv.isUnit_map e.toMulEquiv).mp ?_
    have he : e.toMulEquiv (k : Γ(Sp ℂ, ⊤)) = (k : ℂ) := map_natCast e k
    rw [he]
    exact (Nat.cast_ne_zero.mpr hk).isUnit
  exact GlobalTheory.ConstTheta.torsion_const hc.1 hc.2.2 hu y y₀ hy hy₀ hyj.symm

end GlobalTheory.KS
