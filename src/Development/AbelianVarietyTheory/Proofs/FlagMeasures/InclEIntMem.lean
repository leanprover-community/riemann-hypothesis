module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField
open scoped TensorProduct

noncomputable section
open Classical

namespace GlobalTheory.VectorInclusion

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def vecIncl (x : Fin n → E) : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F :=
  fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)

theorem inclE_int_mem (c : 𝓞 E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E) ∈ Formalism.MainNotions.S.IntAf F E := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩
  rfl

theorem vecIncl_add (x y : Fin n → E) :
    vecIncl (F := F) (x + y) = vecIncl (F := F) x + vecIncl (F := F) y := by
  funext i; simp [vecIncl, map_add (f := _)]

theorem vecIncl_zero : vecIncl (F := F) (0 : Fin n → E) = 0 := by
  funext i; simp [vecIncl]

theorem vecIncl_smul (c : 𝓞 E) (x : Fin n → E) :
    vecIncl (F := F) (c • x) =
      (⟨Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E), inclE_int_mem c⟩ : Formalism.MainNotions.S.IntAf F E) •
        vecIncl (F := F) x := by
  funext i
  simp only [vecIncl, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

theorem lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image (vecIncl (F := F)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    have hxL : x ∈ L := hs ▸ Submodule.subset_span hx
    exact ⟨⟨x, hxL⟩, rfl⟩
  · unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    have key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)),
        vecIncl (F := F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E)
          ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        apply Submodule.subset_span
        simp only [Finset.coe_image]
        exact ⟨z, hz, rfl⟩
      | zero => rw [vecIncl_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [vecIncl_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [vecIncl_smul]; exact Submodule.smul_mem _ _ ha
    rw [← hs] at hx
    exact key x hx

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) :=
  fun L hL => lamAf_fg L hL

end GlobalTheory.VectorInclusion

end
