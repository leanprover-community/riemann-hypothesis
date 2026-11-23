module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CharpolyCont

theorem continuous_eval₂_of {X R : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Type*} (f : ℤ →+* R) (P : MvPolynomial σ ℤ) (x : X → σ → R)
    (hx : ∀ i, Continuous fun t => x t i) : Continuous fun t => MvPolynomial.eval₂ f (x t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add]; exact hP.add hQ
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hP.mul (hx i)

theorem continuous_charpoly_coeff_mulLeft {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [TopologicalSpace A] [IsModuleTopology R A]
    (k : ℕ) : Continuous fun a : A => (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k := by
  let b := Module.Free.chooseBasis R A
  have e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A =>
          LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2)
        ((Matrix.charpoly.univ ℤ (Module.Free.ChooseBasisIndex R A)).coeff k) := by
    intro a
    rw [Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]
    rfl
  simp_rw [e]
  refine continuous_eval₂_of _ _ _ fun ij => ?_
  have h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 =
      (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a := by
    intro a
    simp [LinearMap.toMatrix_apply]
  simp_rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end GlobalTheory.CharpolyCont

open GlobalTheory.CharpolyCont in
theorem GlobalTheory.charpoly_coeff_continuous_GAf : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf =>
    (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C))).coeff k := by
  intro p _ G k
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))
