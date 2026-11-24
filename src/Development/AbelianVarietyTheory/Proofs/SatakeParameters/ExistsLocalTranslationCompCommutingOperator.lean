module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.LocFactor

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem glAf_ext {x y : GL (Fin a) (Af E)}
    (h : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) :
    x = y := by
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun v => ?_)
  have := congrArg (fun m : GL (Fin a) (v.adicCompletion E) => (m.val : Matrix (Fin a) (Fin a) (v.adicCompletion E)) i j) (h v)
  exact this

theorem locGL_comm_away (w : HeightOneSpectrum (𝓞 E)) (k : GL (Fin a) (Af E))
    (h : GL (Fin a) (w.adicCompletion E)) :
    locGL E a w h * ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) =
      ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) * locGL E a w h := by
  refine glAf_ext fun v => ?_
  simp only [map_mul, map_inv]
  by_cases hv : v = w
  · subst hv
    rw [pLoc_locGL, pLoc_locGL, inv_mul_cancel, mul_one, one_mul]
  · rw [pLoc_locGL_of_ne hv, pLoc_locGL_of_ne hv, inv_one, one_mul, one_mul, mul_one]

theorem op_eq_locRep_comp (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : Op E a) :
    ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V),
      (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  cases o with
  | fin k =>
    set kw := GeneralLinearGroup.map (pLoc E w) k
    set k' := (locGL E a w kw)⁻¹ * k
    refine ⟨kw, π.op (.fin k'), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k') (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
        locGL_comm_away]
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (finGL E a k) φ.1 = rt E a (finGL E a (locGL E a w kw)) (rt E a (finGL E a k') φ.1)
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel_left]
  | cpt k =>
    refine ⟨1, π.op (.cpt k), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change rt E a (infGL E a (Unitary.toUnits k)) (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (rt E a (infGL E a (Unitary.toUnits k)) φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, infGL_comm]
    · rw [map_one]; rfl
  | lie X =>
    refine ⟨1, π.op (.lie X), fun h => ?_, ?_⟩
    · refine LinearMap.ext fun φ => Subtype.ext ?_
      change lie E a X (rt E a (finGL E a (locGL E a w h)) φ.1) =
        rt E a (finGL E a (locGL E a w h)) (lie E a X φ.1)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, lie_rt_fin]
    · rw [map_one]; rfl

theorem exists_locRep_comp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a)
    (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E))
    (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T :=
  fun _ _ _ _ _ π w o => op_eq_locRep_comp π w o

end GlobalTheory.LocFactor
