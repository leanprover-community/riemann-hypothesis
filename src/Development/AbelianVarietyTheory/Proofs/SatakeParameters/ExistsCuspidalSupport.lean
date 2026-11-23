module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspidalSupportZero

theorem exists_isCuspSupport_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (π : Irr k 0) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let d : Fin 0 → ℕ := fun a => a.elim0
  let σ : ∀ a, Irr k (d a) := fun a => a.elim0
  refine ⟨0, d, σ, π.irr, fun a => a.elim0, ?_⟩
  let e : (Σ a, Fin (d a)) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  refine ⟨e, ?_⟩
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := k) e (fun a => (σ a).π)
  have hirr := π.irr

  obtain ⟨v₀, hv₀⟩ : ∃ v : π.V, v ≠ 0 := by
    by_contra h
    push_neg at h
    apply (bot_ne_top : (⊥ : Subrepresentation π.π) ≠ ⊤)
    ext v
    simp [h v]
  let L : Subrepresentation π.π := ⟨ℂ ∙ v₀, fun g v hv => by
    rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  have hL : L = ⊤ := by
    rcases eq_bot_or_eq_top L with h | h
    · exfalso
      have : v₀ ∈ L.toSubmodule := Submodule.mem_span_singleton_self v₀
      rw [h] at this
      exact hv₀ ((Submodule.mem_bot ℂ).1 this)
    · exact h
  let f : (multiProd e fun a => (σ a).π).IntertwiningMap π.π :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π.V v₀) ∘ₗ φ.toLinearEquiv.toLinearMap
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]; rfl }
  refine IsSubquotient.of_surjective f fun v => ?_
  have hv : v ∈ L.toSubmodule := by rw [hL]; trivial
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine ⟨φ.toLinearEquiv.symm c, ?_⟩
  show (LinearMap.toSpanSingleton ℂ π.V v₀) (φ.toLinearEquiv (φ.toLinearEquiv.symm c)) = c • v₀
  erw [LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.CuspidalSupportZero
