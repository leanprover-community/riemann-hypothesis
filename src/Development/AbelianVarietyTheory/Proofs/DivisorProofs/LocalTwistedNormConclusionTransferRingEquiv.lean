module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.FinClsLoc

theorem localTransfer : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K K' : Type) [Field K] [Field K'] [Algebra ℚ K] [Algebra ℚ K'],
    (K ≃+* K') → ∀ (Y a b b' : G.C),
    (∃ (u : Kˣ) (z : (K ⊗[ℚ] G.C)ˣ), Commute (z : K ⊗[ℚ] G.C) (inC G K Y) ∧
      inC G K a = algebraMap K (K ⊗[ℚ] G.C) (u : K) * ((z : K ⊗[ℚ] G.C) * inC G K b *
        (starT G.star K (z : K ⊗[ℚ] G.C)).unop * inC G K b')) →
    ∃ (u : K'ˣ) (z : (K' ⊗[ℚ] G.C)ˣ), Commute (z : K' ⊗[ℚ] G.C) (inC G K' Y) ∧
      inC G K' a = algebraMap K' (K' ⊗[ℚ] G.C) (u : K') * ((z : K' ⊗[ℚ] G.C) * inC G K' b *
        (starT G.star K' (z : K' ⊗[ℚ] G.C)).unop * inC G K' b') := by
  intro p _ G K K' _ _ _ _ e Y a b b' ⟨u, z, hc, h⟩
  have hq : ∀ q : ℚ, e (algebraMap ℚ K q) = algebraMap ℚ K' q := fun q =>
    RingHom.congr_fun (Subsingleton.elim ((e : K →+* K').comp (algebraMap ℚ K)) (algebraMap ℚ K')) q
  let e' : K ≃ₐ[ℚ] K' := AlgEquiv.ofRingEquiv (f := e) hq
  let T : K ⊗[ℚ] G.C ≃ₐ[ℚ] K' ⊗[ℚ] G.C := Algebra.TensorProduct.congr e' AlgEquiv.refl
  have hT1 : ∀ c : G.C, T (inC G K c) = inC G K' c := by
    intro c
    simp [T, inC, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  have hT2 : ∀ x : K, T (algebraMap K (K ⊗[ℚ] G.C) x) = algebraMap K' (K' ⊗[ℚ] G.C) (e x) := by
    intro x
    simp [T, e', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
  have hT3 : ∀ w : K ⊗[ℚ] G.C, (starT G.star K' (T w)).unop = T (starT G.star K w).unop := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      have : T (r ⊗ₜ x) = e r ⊗ₜ x := by
        simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rw [this, starT_tmul, starT_tmul]
      simp [T, e', Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]
  refine ⟨Units.map (e : K →* K') u, Units.map (T : K ⊗[ℚ] G.C →* K' ⊗[ℚ] G.C) z, ?_, ?_⟩
  · have := hc.map T
    rw [hT1] at this
    exact this
  · have h' := congrArg T h
    rw [hT1, map_mul, hT2, map_mul, map_mul, map_mul, hT1, hT1, ← hT3] at h'
    simpa using h'

end GlobalTheory.FinClsLoc
