module

public import Development.EtaleCohomology.TateTwists.EtaleTensorPairTwistResolutionMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def tt_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (μ : Pair I J K), μ.IsTensor

def tt_tens_ge : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K), I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → μ.IsTensor →
    K.IsStrictlyGE 0

def tt_twist_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {J M : Cx (ZMod q)}
    (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q j J e' → (∀ t, FlatS (J.X t)) →
    ∀ σ : Pair (sgl (tw q i)) J M, σ.IsTensor →
      IsTwRes q k M fun U ζ => σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) (e' U ζ)

def tt_res_side : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) {I J M T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U),
    IsTwRes q i I e → J.IsStrictlyGE 0 → (∀ t, FlatS (J.X t)) →
    ∀ (σ : Pair (sgl (tw q i)) J M) (τ : Pair I J T), σ.IsTensor → τ.IsTensor →
      ∃ m : M ⟶ T, QuasiIso m ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec (J.X 0) U),
        Sec.map (m.f 0) (σ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) b) =
          τ.mul U 0 0 0 (add_zero 0) (e U ζ) b

theorem etale_tensor_twisted_resolution_of_existence_bound_and_sides (hex : tt_tens_ex) (hge : tt_tens_ge) (htw : tt_twist_side) (hres : tt_res_side) :
    EtaleTensorPairTwistResolutionMul := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨M, σ, hσ⟩ := hex (ZMod q) (sgl (tw q i)) J
  obtain ⟨-, ε₁, hε₁, hgen₁⟩ := htw q i j k hk e' hJ hflat σ hσ
  obtain ⟨m, hm, hgen⟩ := hres q i e hI hJ.1 hflat σ τ hσ hτ
  refine ⟨hge (ZMod q) τ hI.1 hJ.1 hτ, ε₁ ≫ m, inferInstance, fun U ζ => ?_⟩
  refine Eq.trans ?_ (hgen U ζ (e' U ζ))
  refine Eq.trans ?_ (congrArg (Sec.map (m.f 0)) (hgen₁ U ζ))
  rfl

end LateralTheory.EtaleFoundations
