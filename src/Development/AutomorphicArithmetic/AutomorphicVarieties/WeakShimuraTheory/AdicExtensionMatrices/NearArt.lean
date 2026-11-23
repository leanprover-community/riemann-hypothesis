module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.LaurPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.NearOfAdjoin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ScaleRD
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.sxNearArt :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → RD.Graded D W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), IsNilpotent (maximalIdeal R') → Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hnil hQ
  have hc : ∀ i j, -((∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs : ℕ) : ℤ) ≤ τ (wt i j) := by
    intro i j
    have h1 : (τ (wt i j)).natAbs ≤ ∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs :=
      Finset.single_le_sum (f := fun p : Fin 4 × Fin 4 => (τ (wt p.1 p.2)).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i, j))
    omega
  generalize (∑ p : Fin 4 × Fin 4, (τ (wt p.1 p.2)).natAbs) = c at hc
  obtain ⟨S, _, _, _, e, he⟩ := sxLaur (Λ := Λ) hnil c
  obtain ⟨Q', hQ', hr, hψ⟩ := sxScaleRD hnil he hc hQ
  obtain ⟨F, hF, -⟩ := hU.2 S Q' hQ'
  have hFr : ∀ g i j, e (F (D.r g i j)) = HahnSeries.single (τ (wt i j)) (Q.r g i j) := by
    intro g i j
    rw [← hr, ← hF]; rfl
  have hFψ : ∀ v i s, e (F (D.ψ v i s)) = HahnSeries.single 0 (Q.ψ v i s) := by
    intro v i s
    rw [← hψ, ← hF]; rfl
  have hz : ∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y := by
    intro s
    rcases hG.var s with ⟨g, i, j, x, h1, h2, h3⟩ | ⟨v, i, t, x, h1, h2⟩
    · rw [h1, h2, map_sub, map_sub, hFr, AlgHom.commutes, he.alg]
      by_cases hij : i = j
      · rw [(wt_eq_zero i j).2 hij, map_zero]
        exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
      · rw [h3 hij]
        exact ⟨Q.r g i j, by simp⟩
    · rw [h1, h2, map_sub, map_sub, hFψ, AlgHom.commutes, he.alg, map_zero]
      exact ⟨_, (HahnSeries.single_sub _ _ _).symm⟩
  obtain ⟨f, hf⟩ := sxLaurDesc W he τ F (sxLaurPart W hG.max he τ F hz)
  have er : ∀ g i j, ((D'.r g i j : W.A) : R) = D.r g i j := by
    intro g i j
    rw [← hD']; rfl
  have eψ : ∀ v i s, ((D'.ψ v i s : W.A) : R) = D.ψ v i s := by
    intro v i s
    rw [← hD']; rfl
  refine ⟨f, RD.ext ?_ ?_⟩
  · ext g i j
    have hm : D'.r g i j ∈ W.gr (wt i j) := by
      show ((D'.r g i j : W.A) : R) ∈ W.part (wt i j)
      rw [er]; exact hG.ent g i j
    have h := hf _ _ hm
    rw [er, hFr] at h
    exact (HahnSeries.single_injective _ h).symm
  · funext v i
    ext s
    have hm : D'.ψ v i s ∈ W.gr 0 := by
      show ((D'.ψ v i s : W.A) : R) ∈ W.part 0
      rw [eψ]; exact hG.chr v i s
    have h := hf _ _ hm
    rw [eψ, hFψ, map_zero] at h
    exact (HahnSeries.single_injective _ h).symm
