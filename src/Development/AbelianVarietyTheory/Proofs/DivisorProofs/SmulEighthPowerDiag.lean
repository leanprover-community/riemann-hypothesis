module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

theorem smul_eighth_power_diag : ∀ (X₀ X : Type) [AddCommGroup X₀] [AddCommGroup X] (K : (Fin 8 → X₀) ≃+ (Fin 8 → X)), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) → ∃ k : X₀ ≃+ X, ∀ mu, K mu = fun u => k (mu u) := by
  intro X₀ X _ _ K hK
  have hsel : ∀ (Y : Type) [AddCommGroup Y] (w : Fin 8) (nu : Fin 8 → Y),
      (fun u : Fin 8 => ∑ v, (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) u v • nu v)
        = fun _ => nu w := by
    intro Y _ w nu
    funext u
    simp [Matrix.of_apply]
  have hc : ∀ (mu : Fin 8 → X₀) (w : Fin 8), K (fun _ => mu w) = fun _ => K mu w := by
    intro mu w
    have h := hK (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) mu
    rw [hsel, hsel] at h
    exact h
  let f : X₀ →+ X :=
    { toFun := fun x => K (fun _ => x) 0
      map_zero' := by
        show K 0 0 = 0
        simp
      map_add' := by
        intro x y
        show K ((fun _ => x) + (fun _ => y)) 0 = _
        rw [map_add (f := _)]
        rfl }
  have hform : ∀ (mu : Fin 8 → X₀) (u : Fin 8), K mu u = f (mu u) := by
    intro mu u
    show K mu u = K (fun _ => mu u) 0
    rw [hc]
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h1 : K (fun _ => x) = 0 := by
      funext u
      rw [hform]
      exact hx
    have h2 : (fun _ : Fin 8 => x) = 0 := K.injective (h1.trans (map_zero K).symm)
    exact congrFun h2 0
  have surj : Function.Surjective f := by
    intro y
    refine ⟨K.symm (fun _ => y) 0, ?_⟩
    have h := hform (K.symm fun _ => y) 0
    rw [← h]
    simp
  refine ⟨AddEquiv.ofBijective f ⟨inj, surj⟩, fun mu => funext fun u => ?_⟩
  exact hform mu u

end GlobalTheory
