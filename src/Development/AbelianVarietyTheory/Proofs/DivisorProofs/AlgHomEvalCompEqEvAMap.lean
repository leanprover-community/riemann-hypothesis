module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem algHom_eval_comp_eq_evA_map :
    ∀ (p m : ℕ) (O A k A' σ : Type) [CommRing O] [CommRing A] [Algebra O A] [CommRing k]
      [CommRing A'] [Algebra k A'] [Fintype σ] (x : σ → A) (E : MvPowerSeries σ O →ₐ[O] A),
      IsEval p x E → ∀ (r : O →+* k) (g : A →+* A'),
      (∀ c, g (algebraMap O A c) = algebraMap k A' (r c)) → (p : A') ^ m = 0 →
      ∀ hx : ∀ i, IsNilpotent (g (x i)), ∀ f,
        g (E f) = evA k (fun i => g (x i)) hx (map r f) := by
  intro p m O A k A' σ _ _ _ _ _ _ _ x E hE r g hg _ hx f
  letI : Algebra O A' := ((algebraMap k A').comp r).toAlgebra
  have hs : HasSubst (fun i => (C (g (x i)) : MvPowerSeries Empty A')) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using hx i
  have hevX : ∀ i, evA k (fun i => g (x i)) hx (X i) = g (x i) := by
    intro i
    simp [evA, coe_substAlgHom, subst_X hs]
  let φ : MvPowerSeries σ O →ₐ[O] A' :=
    { g.comp E.toRingHom with
      commutes' := fun c => by
        show g (E (algebraMap O _ c)) = (algebraMap k A').comp r c
        rw [AlgHom.commutes, hg]; rfl }
  let ψ : MvPowerSeries σ O →ₐ[O] A' :=
    { (evA k (fun i => g (x i)) hx).toRingHom.comp (map r) with
      commutes' := fun c => by
        show evA k (fun i => g (x i)) hx (map r (algebraMap O _ c)) = (algebraMap k A').comp r c
        have hm : map r (algebraMap O (MvPowerSeries σ O) c) =
            algebraMap k (MvPowerSeries σ k) (r c) := by
          simp [MvPowerSeries.algebraMap_apply, map_C]
        rw [hm, AlgHom.commutes]; rfl }
  have hφX : ∀ i, φ (X i) = g (x i) := fun i => by
    show g (E (X i)) = _
    rw [hE.1 i]
  have hψX : ∀ i, ψ (X i) = g (x i) := fun i => by
    show evA k (fun i => g (x i)) hx (map r (X i)) = _
    rw [map_X, hevX]
  have key := GlobalTheory.mvPowerSeries_algHom_ext_of_isNilpotent O σ A' φ ψ
    (fun i => by rw [hφX]; exact hx i) (fun i => by rw [hφX, hψX])
  exact DFunLike.congr_fun key f

end GlobalTheory
