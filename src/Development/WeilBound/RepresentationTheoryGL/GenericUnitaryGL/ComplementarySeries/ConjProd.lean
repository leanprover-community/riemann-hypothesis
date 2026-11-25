module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ConjProd
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace PositivityTheory.RgGu.NR.ConjProd

def Cj (Y : Type) : Type := Y

instance (Y : Type) [AddCommGroup Y] : AddCommGroup (Cj Y) := inferInstanceAs (AddCommGroup Y)

instance (Y : Type) [AddCommGroup Y] [Module ℂ Y] : Module ℂ (Cj Y) := Module.compHom Y (starRingEnd ℂ)

def semiInv {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) : Y →ₛₗ[starRingEnd ℂ] X where
  toFun := Function.surjInv hφ.2
  map_add' a b := hφ.1 (by rw [map_add (f := _), Function.surjInv_eq hφ.2, Function.surjInv_eq hφ.2,
    Function.surjInv_eq hφ.2])
  map_smul' c y := hφ.1 (by
    rw [Function.surjInv_eq hφ.2, map_smulₛₗ, Function.surjInv_eq hφ.2]
    simp)

theorem semiInv_apply {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (y : Y) : φ (semiInv φ hφ y) = y :=
  Function.surjInv_eq hφ.2 y

theorem semiInv_apply' {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (φ : X →ₛₗ[starRingEnd ℂ] Y) (hφ : Function.Bijective φ) (x : X) : semiInv φ hφ (φ x) = x :=
  hφ.1 (semiInv_apply φ hφ (φ x))

section Tensor

variable {α : Type} [Fintype α] {X Y : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
  [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]

end Tensor

theorem conjEquiv_piTensor {α : Type} [Fintype α] {Γ X Y : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)]
    (π : ∀ a, Representation ℂ (Γ a) (X a)) (σ : ∀ a, Representation ℂ (Γ a) (Y a))
    (h : ∀ a, ConjEquiv (π a) (σ a)) : ConjEquiv (piTensor π) (piTensor σ) := by
  apply CompanionTheory.RgGu.NR.ConjProd.conjEquiv_piTensor <;> assumption

section Ind

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  {n : Type} [Fintype n] [DecidableEq n]

theorem star_deltaHalf (g : Levi k m) : starRingEnd ℂ (deltaHalf k m g : ℂ) = deltaHalf k m g := by
  rw [deltaHalf_apply, Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  have e : ((modExp m a : ℂ) / 2) = (((modExp m a : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  show starRingEnd ℂ (((nabs k (Matrix.GeneralLinearGroup.det (g a)) : ℝ) : ℂ) ^ ((modExp m a : ℂ) / 2)) =
    ((nabs k (Matrix.GeneralLinearGroup.det (g a)) : ℝ) : ℂ) ^ ((modExp m a : ℂ) / 2)
  rw [e, ← Complex.ofReal_cpow (nabs_pos' k _).le, Complex.conj_ofReal]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def indMap (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) V} {τ : Representation ℂ (Levi k m) W}
    (φ : V →ₛₗ[starRingEnd ℂ] W) (hφ : ∀ g v, φ (ρ g v) = τ g (φ v)) :
    IndSp e ρ →ₛₗ[starRingEnd ℂ] IndSp e τ where
  toFun f := ⟨⟨fun g => φ (f.1.1 g), fun p g => by
      show φ (f.1.1 (p * g)) = (deltaHalf k m (leviProj k e p) : ℂ) • τ (leviProj k e p) (φ (f.1.1 g))
      rw [parInd_law e ρ f p g, map_smulₛₗ, star_deltaHalf, hφ]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds f.2 (by simp)) fun g hg => by
      have hg' : ind (parab k e) ((twist ρ (deltaHalf k m)).comp (leviProj k e)) g f.1 = f.1 := hg
      apply Subtype.ext
      funext x
      exact congrArg φ (congrFun (congrArg Subtype.val hg') x))⟩
  map_add' f f' := by
    apply Subtype.ext; apply Subtype.ext; funext g
    exact map_add φ (f.1.1 g) (f'.1.1 g)
  map_smul' c f := by
    apply Subtype.ext; apply Subtype.ext; funext g
    exact map_smulₛₗ φ c (f.1.1 g)

theorem conjEquiv_parInd (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) V)
    (τ : Representation ℂ (Levi k m) W) (h : ConjEquiv ρ τ) : ConjEquiv (parInd e ρ) (parInd e τ) := by
  apply CompanionTheory.RgGu.NR.ConjProd.conjEquiv_parInd <;> assumption

end Ind

end PositivityTheory.RgGu.NR.ConjProd

namespace PositivityTheory.RgGu.NR

open ConjProd in
theorem conjProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjProd k := by
  intro h N d hd X Y _ _ _ _ π σ hc
  exact conjEquiv_parInd _ _ _ (conjEquiv_piTensor π σ hc)

end PositivityTheory.RgGu.NR

end
