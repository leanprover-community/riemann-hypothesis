module

public import Mathlib.Algebra.DualNumber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.PUnit
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory GlobalTheory.ZH
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open TensorProduct

namespace GlobalTheory.TangentCrit

theorem formallyUnramified_of_dual_const_field {K A B : Type} [Field K] [IsAlgClosed K]
    [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FiniteType K B] [Algebra.FiniteType A B]
    (H : ∀ φ : B →+* DualNumber K, (∀ c, φ (algebraMap K B c) = algebraMap K (DualNumber K) c) →
      (∀ a, (φ (algebraMap A B a)).snd = 0) → ∀ b, (φ b).snd = 0) :
    Algebra.FormallyUnramified A B := by
  refine ⟨?_⟩
  by_contra hne
  rw [← Module.support_eq_empty_iff (R := B), ← ne_eq, ← Set.nonempty_iff_ne_empty] at hne
  obtain ⟨p, hp⟩ := hne
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let P : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  have hP : P ∈ Module.support B Ω[B⁄A] := by
    rw [Module.support_eq_zeroLocus] at hp ⊢
    exact fun x hx => hpm (hp hx)
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hP
  have hsurj : Function.Surjective (algebraMap B m.ResidueField) := by
    intro y
    obtain ⟨x, rfl⟩ := m.bijective_algebraMap_quotient_residueField.surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨b, rfl⟩
  haveI : Algebra.FiniteType K m.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom K B m.ResidueField) hsurj
  haveI : Module.Finite K m.ResidueField := finite_of_finite_type_of_isJacobsonRing K _
  let ev : m.ResidueField →ₐ[K] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra m.ResidueField K := ev.toRingHom.toAlgebra
  letI : Algebra B K := (ev.toRingHom.comp (algebraMap B m.ResidueField)).toAlgebra
  haveI : IsScalarTower B m.ResidueField K := .of_algebraMap_eq fun _ => rfl
  letI : Algebra A K := ((algebraMap B K).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B K := .of_algebraMap_eq fun _ => rfl
  have key : Function.Injective ((0 : Ω[B⁄A] →ₗ[B] PUnit.{1}).lTensor m.ResidueField) :=
    lTensor_injective_of_extend (k := K) _ fun χ => by
      refine ⟨0, ?_⟩
      let D : Derivation A B K := χ.compDer (KaehlerDifferential.D A B)
      have hlin : ∀ c, derToDual D (algebraMap K B c) = algebraMap K (DualNumber K) c := by
        intro c
        ext
        · rw [fst_derToDual]
          change ev (algebraMap B m.ResidueField (algebraMap K B c)) = _
          rw [← IsScalarTower.algebraMap_apply, ev.commutes]
          rfl
        · rw [snd_derToDual, IsScalarTower.algebraMap_apply K A B, D.map_algebraMap]
          rfl
      have := H (derToDual D) hlin (fun a => (snd_derToDual D _).trans (D.map_algebraMap a))
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
      have := this b
      rw [snd_derToDual] at this
      simpa [D] using this.symm
  obtain ⟨z, hz⟩ := exists_ne (0 : m.ResidueField ⊗[B] Ω[B⁄A])
  exact hz (key (by simp))

end GlobalTheory.TangentCrit

namespace GlobalTheory.TangentCrit

end GlobalTheory.TangentCrit
