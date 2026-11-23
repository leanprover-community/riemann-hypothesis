module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesOneAddConstMulXMulInv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjective
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

open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => Img.isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← Img.map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← Img.map_sh, ← Img.map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← Img.map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]
