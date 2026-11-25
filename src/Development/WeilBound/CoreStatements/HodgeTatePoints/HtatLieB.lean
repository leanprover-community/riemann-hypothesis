module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChart
public import Mathlib.RingTheory.RingHom.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieChartOfSmoothChart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorOfDualHom
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorSumDualNumber
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ChartDer

noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

theorem mul_left_eq : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (U : G.left.Opens) (hU : IsAffineOpen U)
  (C : Type) [CommRing C] (y : Sp C ⟶ S) (u : Γ(G.left, U) →+* C),
  (1 : Over.mk y ⟶ G).left = spMap u ≫ hU.fromSpec →
  ∀ (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
  ∀ φ ψ χ : Γ(G.left, U) →+* DualNumber C, (∀ a, (φ a).fst = u a) → (∀ a, (ψ a).fst = u a) → (∀ a, (χ a).fst = u a) →
    (∀ a, (χ a).snd = (φ a).snd + (ψ a).snd) →
    v.left = spMap φ ≫ hU.fromSpec → w.left = spMap ψ ≫ hU.fromSpec → (v * w).left = spMap χ ≫ hU.fromSpec :=
  _root_.GlobalTheory.CompanionTheory.Ar.TanMul.mul_left_eq

theorem exists_lieModel {S : Scheme.{0}} (G : Over S) [GrpObj G] (U : G.left.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V)
    (C : Type) [CommRing C] (y : Sp C ⟶ S) (v : Γ(G.left, U) →+* C)
    (h1 : (1 : Over.mk y ⟶ G).left = spMap v ≫ hU.fromSpec)
    {E : Type} [AddCommGroup E] [Module C E] (δ : E → Γ(G.left, U) → C)
    (hadd : ∀ e a b, δ e (a + b) = δ e a + δ e b)
    (hmul : ∀ e a b, δ e (a * b) = v a * δ e b + v b * δ e a)
    (hker : ∀ e b, δ e ((G.hom.appLE V U hUV).hom b) = 0)
    (hEadd : ∀ e e' a, δ (e + e') a = δ e a + δ e' a)
    (hEsmul : ∀ (c : C) e a, δ (c • e) a = c * δ e a)
    (hinj : ∀ e e', (∀ a, δ e a = δ e' a) → e = e')
    (hsurj : ∀ δ' : Γ(G.left, U) → C, (∀ a b, δ' (a + b) = δ' a + δ' b) →
      (∀ a b, δ' (a * b) = v a * δ' b + v b * δ' a) →
      (∀ b, δ' ((G.hom.appLE V U hUV).hom b) = 0) → ∃ e, ∀ a, δ e a = δ' a) :
    ∃ M : LieModel G y E, ∀ e, ∃ φ : Γ(G.left, U) →+* DualNumber C,
      (∀ a, (φ a).fst = v a) ∧ (∀ a, (φ a).snd = δ e a) ∧ (M.pt e).left = spMap φ ≫ hU.fromSpec := by
  obtain ⟨c1, c2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.TanChart.tan_iff_der S G U V hU hV hUV C y v h1
  let φ : E → (Γ(G.left, U) →+* DualNumber C) := fun e => dualOf v (δ e) (hadd e) (hmul e)
  have φfst : ∀ e a, (φ e a).fst = v a := fun e a => dualOf_fst ..
  have φsnd : ∀ e a, (φ e a).snd = δ e a := fun e a => dualOf_snd ..
  have ex : ∀ e, ∃ t : epsAt y ⟶ G, IsTanAt G y t ∧ t.left = spMap (φ e) ≫ hU.fromSpec :=
    fun e => c1 (φ e) (φfst e) fun b => by rw [φsnd, hker]
  choose pt ptan pleft using ex
  have spinj : ∀ ψ ψ' : Γ(G.left, U) →+* DualNumber C,
      spMap ψ ≫ hU.fromSpec = spMap ψ' ≫ hU.fromSpec → ψ = ψ' := fun ψ ψ' h => by
    have h2 := Spec.map_injective ((cancel_mono hU.fromSpec).1 h)
    simpa using congrArg CommRingCat.Hom.hom h2
  refine ⟨{ pt := pt, tan := ptan, inj := ?_, onto := ?_, add := ?_, smul := ?_ },
    fun e => ⟨φ e, φfst e, φsnd e, pleft e⟩⟩
  · intro e e' h
    have h2 := spinj _ _ (by rw [← pleft, ← pleft, h] : spMap (φ e) ≫ hU.fromSpec = spMap (φ e') ≫ hU.fromSpec)
    exact hinj _ _ fun a => by rw [← φsnd, h2, φsnd]
  · intro t ht
    obtain ⟨ψ, f1, f2, f3⟩ := c2 t ht
    obtain ⟨e, he⟩ := hsurj (fun a => (ψ a).snd) (fun a b => by simp)
      (fun a b => by
        simp only [map_mul, TrivSqZeroExt.snd_mul, f1]
        simp [mul_comm, add_comm]) f2
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    have h2 : φ e = ψ := RingHom.ext fun a => TrivSqZeroExt.ext (by rw [φfst, f1]) (by rw [φsnd, he])
    rw [pleft, f3, h2]
  · intro e e'
    refine Over.OverMorphism.ext ?_
    rw [mul_left_eq S G U hU C y v h1 (pt e) (pt e') (ptan e) (ptan e') (φ e) (φ e') (φ (e + e'))
      (φfst e) (φfst e') (φfst _) (fun a => by rw [φsnd, φsnd, φsnd, hEadd]) (pleft e) (pleft e'), pleft]
  · intro c e
    have h2 : φ (c • e) = (epsMul c).comp (φ e) := RingHom.ext fun a => TrivSqZeroExt.ext
      (by simp [epsMul, φfst]) (by simp [epsMul, φsnd, hEsmul])
    rw [pleft, pleft, h2, spMap_comp, Category.assoc]

theorem lieChart_of_smooth_chart : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Sp R ⟶ S) (f : R) (U : G.left.Opens) (V : S.Opens)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ G.hom ⁻¹ᵁ V), RingHom.Smooth (G.hom.appLE V U hUV).hom →
  ∀ u : Γ(G.left, U) →+* Localization.Away f,
    (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec → LieChart G x f := by
  apply GlobalTheory.CompanionTheory.Ar.ChartDer.lieChart_of_smooth_chart

end PositivityTheory.HtPt.Htat.Lie
