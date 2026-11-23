module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelScale
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k3F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K3 h k → SelmerSpannedByKappaLaurent h k := by
  intro l _ L G G0 h n x k hK z hz hb
  obtain ⟨s₀, hs⟩ := selScale l L G G0 h n x false z hz hb
  obtain ⟨z', hz', hzz⟩ := hs s₀ le_rfl
  obtain ⟨s', c, Y, hY, hYt, hYe⟩ := hK z' hz'
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  have hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f := by
    intro a M
    ext i j
    simp
  have key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) =
      x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y := by
    intro g
    have e := congrFun hYe g
    simpa [dY, Finset.sum_apply] using e
  have key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g =
      x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f := by
    intro g
    have e := congrArg f.mapMatrix (key g)

    simpa [map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply] using e
  set u := (f x.t ^ (s' + s₀))⁻¹ with hu
  refine ⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hY i j
    refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
    have h3 := h1 hij
    rw [Submodule.mem_bot] at h3 ⊢
    simp [h3]
  · ext i j
    have h3 := congrFun (congrFun hYt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h3
    simp [Matrix.transpose_apply, h3]
  · funext g
    have e := key2 g
    rw [hzz g, smul_smul, ← pow_add] at e
    simp only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]
    simp [smul_smul]
