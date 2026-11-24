module

public import Formalism.LocalToGlobal.Divisibility.DefGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.FrameCong

theorem coord_mem_idS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : IsFrame β Λ)
    (I : Ideal (𝓞 E)) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hw : w ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) :
    ∀ i, ∃ s ∈ idS F I, (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F) := by
  refine Submodule.span_induction (p := fun w _ => ∀ i, ∃ s ∈ idS F I,
    (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ w) i =
      (s : E ⊗[F] Formalism.L2.Herm.Af F)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨m, hm, rfl⟩
    refine Submodule.smul_induction_on (p := fun m => ∀ i, ∃ s ∈ idS F I,
      (((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
        (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m k))) i = (s : E ⊗[F] Formalism.L2.Herm.Af F)) hm ?_ ?_
    · intro a ha u hu i
      have hu' : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
        Submodule.subset_span ⟨u, hu, rfl⟩
      have t := (hβ _).1 hu' i
      refine ⟨oToS F E a * ⟨_, t⟩, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
      have e : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k)) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) • (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)) := by
        funext k
        show Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((a • u) k) =
          (oToS F E a : E ⊗[F] Formalism.L2.Herm.Af F) * Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (u k)
        rw [Pi.smul_apply, Algebra.smul_def, map_mul]
        rfl
      rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rfl
    · intro m1 m2 h1 h2 i
      obtain ⟨s1, hs1, e1⟩ := h1 i
      obtain ⟨s2, hs2, e2⟩ := h2 i
      refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
      have : (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) ((m1 + m2) k)) =
          (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m1 k)) +
            (fun k => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (m2 k)) := by
        funext k; simp [map_add (f := _)]
      rw [this, Matrix.mulVec_add, Pi.add_apply, e1, e2]
      rfl
  · intro i
    exact ⟨0, zero_mem _, by simp⟩
  · intro a b _ _ ha hb i
    obtain ⟨s1, hs1, e1⟩ := ha i
    obtain ⟨s2, hs2, e2⟩ := hb i
    refine ⟨s1 + s2, add_mem hs1 hs2, ?_⟩
    rw [Matrix.mulVec_add, Pi.add_apply, e1, e2]
    rfl
  · intro c a _ ha i
    obtain ⟨s, hs, e⟩ := ha i
    refine ⟨c * s, Ideal.mul_mem_left _ _ hs, ?_⟩
    rw [show c • a = (c : E ⊗[F] Formalism.L2.Herm.Af F) • a from rfl, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, e]
    rfl

theorem redFn_eq_one_of_congr : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ →
    x ∈ Formalism.L2.DIV.St β → ∀ (I : Ideal (𝓞 E)), (∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ z - z ∈ Formalism.L2.Herm.hatL (F := F) (I • Λ)) →
    ∀ (PP : Formalism.L2.DIV.Pl E), I ≤ PP.asIdeal → Formalism.L2.DIV.redFn β PP x = 1 := by
  intro F E _ _ _ _ _ n β x Λ hβ hx I hcong PP hPP
  classical
  obtain ⟨y, rfl⟩ := hx
  rw [redFn_frGL]
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) := (intGL F E n y).1 with hY
  have e1 : ((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = β.1 * Y * (β⁻¹).1 := rfl
  apply Units.ext
  ext i j
  have hv : β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
    refine (hβ _).2 fun k => ?_
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hkj : k = j
    · subst hkj; simp only [Pi.single_eq_same]; exact Subring.one_mem _
    · rw [Pi.single_eq_of_ne hkj]; exact Subring.zero_mem _
  obtain ⟨s, hs, es⟩ := coord_mem_idS β Λ hβ I _ (hcong _ hv) i
  have hcomp : ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ
        (β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) -
        β.1 *ᵥ (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)) = (Y - 1) *ᵥ Pi.single j 1 := by
    have hm1 : (β⁻¹).1 * (β.1 * Y * (β⁻¹).1) * β.1 = Y := by
      simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [e1, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm1, Units.inv_mul,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hcomp, Matrix.mulVec_single_one, Matrix.col_apply] at es
  have e5 : (((y.1 - 1) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (Y - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hs' : (y.1 - 1) i j = s := Subtype.ext (e5.trans es)
  have hmem : (y.1 - 1) i j ∈ idS F PP.asIdeal := hs' ▸ Ideal.map_mono hPP hs
  have e6 : resS F PP ((y.1 - 1) i j) = 0 := by
    unfold resS
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero]
  show resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at e6
  rw [e6, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.FrameCong
