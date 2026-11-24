module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsFinsetSeparating
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace

@[expose] public section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

namespace GlobalTheory.CompanionTheory.CTFin.ProdTrick

theorem exists_finset_separating {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ V] :
    ∃ T : Finset X, ∀ v ∈ V, (∀ x ∈ T, v x = 0) → v = 0 :=
  _root_.UpperTheory.Reformulated.B.Qp2.exists_finset_separating V

theorem exists_finiteDimensional_of_slices :
    ∀ (X Y : Type) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)),
      FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ →
      ∃ 𝓥 : Submodule ℂ (X × Y → ℂ), FiniteDimensional ℂ 𝓥 ∧
        ∀ f : X × Y → ℂ, (∀ y, (fun x => f (x, y)) ∈ V₁) → (∀ x, (fun y => f (x, y)) ∈ V₂) →
          f ∈ 𝓥 := by
  intro X Y V₁ V₂ h₁ h₂
  obtain ⟨T, hT⟩ := exists_finset_separating V₁
  let S : Submodule ℂ (X × Y → ℂ) :=
    { carrier := {f | (∀ y, (fun x => f (x, y)) ∈ V₁) ∧ (∀ x, (fun y => f (x, y)) ∈ V₂)}
      add_mem' := fun {a b} ha hb =>
        ⟨fun y => V₁.add_mem (ha.1 y) (hb.1 y), fun x => V₂.add_mem (ha.2 x) (hb.2 x)⟩
      zero_mem' := ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩
      smul_mem' := fun c a ha =>
        ⟨fun y => V₁.smul_mem c (ha.1 y), fun x => V₂.smul_mem c (ha.2 x)⟩ }
  let L : S →ₗ[ℂ] (T → V₂) :=
    { toFun := fun f t => ⟨fun y => (f : X × Y → ℂ) ((t : X), y), f.2.2 t⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    funext ⟨x, y⟩
    have hy := hT _ (f.2.1 y) (fun t ht => by
      have := congrArg Subtype.val (congrFun hf ⟨t, ht⟩)
      exact congrFun this y)
    exact congrFun hy x
  have : FiniteDimensional ℂ S := FiniteDimensional.of_injective L hL
  exact ⟨S, this, fun f h1 h2 => ⟨h1, h2⟩⟩

end GlobalTheory.CompanionTheory.CTFin.ProdTrick
