module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGS
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.LocalField Function

noncomputable section

universe u

section Units

variable {K : Type*} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

theorem sq_mem_unitsOutsidePos {u : IdeleGroup K} (hu : u ∈ unitsOutside S) :
    u ^ 2 ∈ unitsOutsidePos S := by
  refine mem_unitsOutsidePos.2 ⟨pow_mem hu 2, fun w ↦ ?_⟩
  rw [map_pow, Units.val_pow_eq_pow_val, map_pow]
  have h0 : InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((infiniteProj w.1 u : (w.1.Completion)ˣ) : w.1.Completion) ≠ 0 :=
    (map_ne_zero _).2 (Units.ne_zero _)
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))

theorem mem_unitsOutsidePos_of_isTotallyComplex [_root_.NumberField.IsTotallyComplex K] {u : IdeleGroup K}
    (hu : u ∈ unitsOutside S) : u ∈ unitsOutsidePos S :=
  mem_unitsOutsidePos.2 ⟨hu, fun w ↦
    absurd w.2 (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1))⟩

end Units

theorem eq_one_of_sq_eq_one_of_odd {G : Type*} [Group G] {n : ℕ} (hn : Odd n) {z : G}
    (h2 : z ^ 2 = 1) (hz : z ^ n = 1) : z = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hz
  exact hz

variable {K : Type u} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ)

def precompPos :
    (SIdeleClassGroup S →* Multiplicative (ZMod n)) →* (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) where
  toFun f := f.comp (SIdeleClassGroupPos.toSIdeleClassGroup S)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem precompPos_apply (f : SIdeleClassGroup S →* Multiplicative (ZMod n)) (x : IdeleGroup K) :
    precompPos S n f (SIdeleClassGroupPos.mk S x) = f (SIdeleClassGroup.mk S x) :=
  rfl

theorem precompPos_injective : Injective (precompPos S n) := fun _ _ h ↦
  (MonoidHom.cancel_right (SIdeleClassGroupPos.toSIdeleClassGroup_surjective S)).1 h

theorem precompPos_surjective (h : Odd n ∨ IsTotallyComplex K) : Surjective (precompPos S n) := by
  intro ψ
  have hle : sIdeleSubgroup S ≤ (ψ.comp (SIdeleClassGroupPos.mk S)).ker := by
    refine sup_le ?_ fun u hu ↦ ?_
    · rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, SIdeleClassGroupPos.mk_diagonal, map_one]
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
      rcases h with hn | hK
      · refine eq_one_of_sq_eq_one_of_odd hn ?_ (zmod_pow_eq_one _)
        rw [← map_pow, ← map_pow, SIdeleClassGroupPos.mk_eq_one_of_mem S (sq_mem_unitsOutsidePos hu),
          map_one]
      · rw [SIdeleClassGroupPos.mk_eq_one_of_mem S (mem_unitsOutsidePos_of_isTotallyComplex hu),
          map_one]
  exact ⟨QuotientGroup.lift _ _ hle, QuotientGroup.monoidHom_ext _ (MonoidHom.ext fun _ ↦ rfl)⟩

def precompPosEquiv (h : Odd n ∨ IsTotallyComplex K) :
    (SIdeleClassGroup S →* Multiplicative (ZMod n)) ≃* (SIdeleClassGroupPos S →* Multiplicative (ZMod n)) :=
  MulEquiv.ofBijective (precompPos S n) ⟨precompPos_injective S n, precompPos_surjective S n h⟩

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω]


variable (Ω) {S n} in
def charEquiv [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K) :
    ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n)) ≃*
      (SIdeleClassGroup S →* Multiplicative (ZMod n)) :=
  (charEquivPos Ω hS).trans (precompPosEquiv S n h).symm

variable {S n}

theorem precompPos_charEquiv [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n]
    (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n))) :
    precompPos S n (charEquiv Ω hS h χ) = charToSIdelePos χ :=
  (precompPosEquiv S n h).apply_symm_apply _

theorem charEquiv_mk_eq [IsAlgClosure K Ω] (hS : S.Finite) [NeZero n] (h : Odd n ∨ IsTotallyComplex K)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K Ω S) (Multiplicative (ZMod n))) (x : IdeleGroup K)
    (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (artinMap K Ω (IdeleClassGroup.mk K x) ⟨y, hy⟩ : Ω)) :
    charEquiv Ω hS h χ (SIdeleClassGroup.mk S x) =
      χ (AlgEquiv.restrictNormalHom (maxUnramifiedOutside K Ω S) g) := by
  rw [← precompPos_apply, precompPos_charEquiv, charToSIdelePos_mk_eq χ x g hg]

variable (S n)

end

end GroundTheory.ProfCoh
