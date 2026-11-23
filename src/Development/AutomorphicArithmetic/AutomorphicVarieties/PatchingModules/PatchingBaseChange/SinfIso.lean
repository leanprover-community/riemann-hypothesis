module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMvps
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem UpperTheory.V.Pa.BC.mvps_congr (K A B σ : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (e : A ≃ₐ[K] B) :
    ∃ E : MvPowerSeries σ A ≃ₐ[K] MvPowerSeries σ B, ∀ a, E a = MvPowerSeries.map (e : A →+* B) a := by
  have h1 : ∀ φ : MvPowerSeries σ A,
      MvPowerSeries.map (e.symm : B →+* A) (MvPowerSeries.map (e : A →+* B) φ) = φ := by
    intro φ
    ext n
    simp
  have h2 : ∀ φ : MvPowerSeries σ B,
      MvPowerSeries.map (e : A →+* B) (MvPowerSeries.map (e.symm : B →+* A) φ) = φ := by
    intro φ
    ext n
    simp
  let f : MvPowerSeries σ A ≃+* MvPowerSeries σ B :=
    { toFun := MvPowerSeries.map (e : A →+* B)
      invFun := MvPowerSeries.map (e.symm : B →+* A)
      left_inv := h1
      right_inv := h2
      map_mul' := map_mul _
      map_add' := map_add _ }
  refine ⟨AlgEquiv.ofRingEquiv (f := f) ?_, fun a => ?_⟩
  · intro k
    simp [f, MvPowerSeries.algebraMap_apply]
  · rfl

theorem UpperTheory.V.Pa.BC.sinf_iso :
    ∀ (l : ℕ) (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D q n : ℕ) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D), (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) → ∃ τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n, SinfRel l τ τS := by
  intro l O O' _ _ _ _ _ D q n τ hτ
  obtain ⟨τ0, h0ι, -, -, h0c⟩ :=
    UpperTheory.V.Pa.BC.til_mvps O O' (abelian₂ O Empty D) (Fin q × Fin n)
  obtain ⟨E, hE⟩ :=
    UpperTheory.V.Pa.BC.mvps_congr O' (Til O O' (abelian₂ O Empty D)) (abelian₂ O' Unit D) (Fin q × Fin n) τ
  have key : ∀ x : MvPowerSeries (Fin q × Fin n) (abelian₂ O Empty D),
      (τ0.trans E) (Til.ι O O' _ x) = MvPowerSeries.map ((τ : _ →+* _).comp (Til.ι O O' _)) x := by
    intro x
    rw [AlgEquiv.trans_apply, h0ι, hE, ← RingHom.comp_apply, ← MvPowerSeries.map_comp]
  refine ⟨τ0.trans E, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro p
    rw [key, MvPowerSeries.map_X]
  · intro a
    rw [key, MvPowerSeries.map_C, RingHom.comp_apply]
    simp [hτ]
  · intro c hc z
    rw [AlgEquiv.trans_apply, hE, MvPowerSeries.constantCoeff_map, h0c c hc z]
    rfl
  · intro a
    unfold delIdeal
    rw [Ideal.map_span, ← Set.range_comp]
    congr 1
    congr 1
    funext p
    simp only [Function.comp_apply, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      AlgEquiv.coe_toRingEquiv, key, map_sub, map_pow, map_add, map_one, MvPowerSeries.map_X]
