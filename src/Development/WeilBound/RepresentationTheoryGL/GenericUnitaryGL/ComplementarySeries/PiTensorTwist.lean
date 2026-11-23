module

import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PiTensorTwist
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealExponentAbsSmoothCharacterLocalField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RgGu.NR

namespace Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {y z : Fin h → IrrGL (k := k)} (e : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr z hz)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem piTensor_twist (x : IrrGL (k := k)) (s : ℝ) :
    piTensor (fun a : Fin 2 => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))) =
      twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) := by
  ext g : 1
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  have ht : ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
      (χ : GL (Fin n) k →* ℂˣ) (g : GL (Fin n) k), twist ρ χ g = ((χ g : ℂ) • ρ g) := fun _ _ _ => rfl
  have ht2 : ∀ (g : Levi k fun _ : Fin 2 => Fin x.1), twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) g =
      ((chi k x.1 s g : ℂ) • (piTensor fun _ : Fin 2 => x.rep) g) := fun _ => rfl
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, ht, ht2, LinearMap.smul_apply]
  rw [MultilinearMap.map_smul_univ]
  congr 1
  simp [chi, Fin.prod_univ_two, Units.val_mul]

end Model

open Model in
theorem prodModel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ProdModel k := by
  apply CompanionTheory.RgGu.NR.prodModel <;> assumption

theorem cuspUnit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CuspUnit k := by
  apply CompanionTheory.RgGu.NR.cuspUnit <;> assumption

end PositivityTheory.RgGu.NR

end
