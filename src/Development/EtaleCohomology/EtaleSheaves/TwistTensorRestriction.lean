module

public import Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ZModFlatnessFromBaerCriterion

def TensTwRes : Prop := ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)}
  (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U),
  IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor →
  IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def LeafInjSecInj : Prop := ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M] (U : Scheme.{0}),
  Module.Injective (ULift.{1} (ZMod q)) (Sec M U)

def LeafInjFlatZMod : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

theorem flatS_of_sec {R : Type} [CommRing R] (M : Shv R)
    (h : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} R) (Sec M U)) : FlatS M := by
  refine ⟨M.obj, 𝟙 M.obj, fun U y => ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x hx => ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => ?_⟩, fun U _ => h U⟩
  have hx' : x = 0 := hx
  subst hx'
  exact map_zero _

instance resGE (q : ℕ) (i : ℤ) : (res (ZMod q) (tw q i)).IsStrictlyGE 0 := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem res_isTwRes (q : ℕ) [NeZero q] (i : ℤ) :
    IsTwRes q i (res (ZMod q) (tw q i)) (fun _ ζ => resGen i ζ) := by
  refine ⟨resGE q i, resAug (tw q i), ?_, fun U ζ => ?_⟩
  · unfold resAug
    exact (inferInstance : QuasiIso (injectiveResolution (tw q i)).ι')
  · simp only [resGen, resι, sglι, Sec.map]
    rfl

theorem res_flat (hA : LeafInjSecInj) (hB : LeafInjFlatZMod) (q : ℕ) [NeZero q] (j t : ℤ) :
    FlatS ((res (ZMod q) (tw q j)).X t) := by
  refine flatS_of_sec _ fun U => hB q _ ?_
  have : Injective ((res (ZMod q) (tw q j)).X t) := by
    unfold res; infer_instance
  exact hA q _ U

end LateralTheory.E.ZModFlatnessFromBaerCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of (h97 : TensTwRes) (hA : LeafInjSecInj) (hB : LeafInjFlatZMod) :
    LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := by
  intro q _ i j T τ hτ
  exact h97 q i j (i + j) rfl (fun _ ζ => resGen i ζ) (fun _ ζ => resGen j ζ) (res_isTwRes q i) (res_isTwRes q j)
    (res_flat hA hB q j) τ hτ
