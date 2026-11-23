module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLinearHomPull
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.SurjOfCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem bracket_symbol_rescale_twist : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (δ₀ : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Λ : Matrix (Fin n) (Fin n) (FractionRing Ω)) (q b c : FractionRing Ω) (k : ℕ), q ≠ 0 → (k : FractionRing Ω) * (q ^ k * b) * ((q ^ k * b) * δ₀ (q ^ k * c) - (q ^ k * c) * δ₀ (q ^ k * b)) - ∑ a, ∑ e, Λ a e * δL a (q ^ k * b) * ((q ^ k * b) * δL e (q ^ k * c) - (q ^ k * c) * δL e (q ^ k * b)) = q ^ (3 * k) * ((k : FractionRing Ω) * b * (b * (δ₀ c - ∑ a, ∑ e, Λ a e * δL a q / q * δL e c) - c * (δ₀ b - ∑ a, ∑ e, Λ a e * δL a q / q * δL e b)) - ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
  intro Ω _ _ n δ₀ δL Λ q b c k hq
  have hpow : ∀ (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (x : FractionRing Ω),
      d (q ^ k * x) = q ^ k * (d x + (k : FractionRing Ω) * x * (d q / q)) := by
    intro d x
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    cases k with
    | zero => simp
    | succ k =>
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
      field_simp
      ring
  have hbr : ∀ d : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      (q ^ k * b) * d (q ^ k * c) - (q ^ k * c) * d (q ^ k * b)
        = q ^ k * q ^ k * (b * d c - c * d b) := by
    intro d
    rw [hpow d b, hpow d c]
    ring
  have h3 : q ^ (3 * k) = q ^ k * q ^ k * q ^ k := by ring
  simp only [hbr]
  simp only [hpow _ b]
  have hs : ∑ a, ∑ e, Λ a e * (q ^ k * (δL a b + (k : FractionRing Ω) * b * (δL a q / q))) *
        (q ^ k * q ^ k * (b * δL e c - c * δL e b))
      = q ^ k * q ^ k * q ^ k * ((k : FractionRing Ω) * b *
          (b * (∑ a, ∑ e, Λ a e * δL a q / q * δL e c)
            - c * (∑ a, ∑ e, Λ a e * δL a q / q * δL e b))
          + ∑ a, ∑ e, Λ a e * δL a b * (b * δL e c - c * δL e b)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs, h3]
  ring

end GlobalTheory.Heat
