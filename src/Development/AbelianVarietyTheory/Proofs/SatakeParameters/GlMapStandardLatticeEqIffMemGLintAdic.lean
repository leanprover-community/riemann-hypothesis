module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt
public import Formalism.SatakeDualWeyl.StatementE
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.LatHecke

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem mem_std_of_coord {x : Fin r → K} (hx : ∀ i, ∃ a : O, algebraMap O K a = x i) :
    x ∈ (std O K r).1 := by
  choose a ha using hx
  have hsum : x = ∑ i, a i • Pi.basisFun K (Fin r) i := by
    ext j
    simp [Finset.sum_apply, Algebra.smul_def, Pi.single_apply, ha]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

theorem entry_of_glMap_std_le {g : GL (Fin r) K} (h : glMap g (std O K r).1 ≤ (std O K r).1)
    (i j : Fin r) : ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j := by
  have hmem : Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) (Pi.basisFun K (Fin r) j) ∈
      glMap g (std O K r).1 :=
    ⟨_, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  obtain ⟨a, ha⟩ := coord_of_mem_std (h hmem) i
  exact ⟨a, by simpa [Matrix.toLin'_apply] using ha⟩

theorem glMap_std_le_of_entry {g : GL (Fin r) K}
    (h : ∀ i j, ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j) :
    glMap g (std O K r).1 ≤ (std O K r).1 := by
  rintro _ ⟨x, hx, rfl⟩
  refine mem_std_of_coord fun i => ?_
  choose a ha using h
  choose b hb using coord_of_mem_std hx
  refine ⟨∑ j, a i j * b j, ?_⟩
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, ha, hb]

theorem glMap_std_eq_iff_entry (g : GL (Fin r) K) :
    glMap g (std O K r).1 = (std O K r).1 ↔
      (∀ i j, ∃ a : O, algebraMap O K a = (g : Matrix (Fin r) (Fin r) K) i j) ∧
      (∀ i j, ∃ a : O, algebraMap O K a = ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j) := by
  constructor
  · intro h
    have h' : glMap g⁻¹ (std O K r).1 = (std O K r).1 := by
      have := congrArg (glMap g⁻¹) h
      rw [← glMap_mul, inv_mul_cancel, glMap_one] at this
      exact this.symm
    exact ⟨entry_of_glMap_std_le h.le, entry_of_glMap_std_le h'.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm (glMap_std_le_of_entry h1) ?_
    have := Submodule.map_mono (f := (Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O)
      (glMap_std_le_of_entry h2)
    have e : glMap g (glMap g⁻¹ (std O K r).1) = (std O K r).1 := by
      rw [← glMap_mul, mul_inv_cancel, glMap_one]
    exact e.ge.trans this

end Dvr

section Sub

variable {L : Type} [Field L] {n : ℕ}

theorem mem_GLint_iff_entry (S : Subring L) (g : GL (Fin n) L) :
    g ∈ GLint (Fin n) S ↔ (∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ S) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ S) := by
  constructor
  · have key : ∀ u : GL (Fin n) S, ∀ i j,
        ((bc (n := Fin n) S.subtype u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ S :=
      fun u i j => ((u : Matrix (Fin n) (Fin n) S) i j).2
    rintro ⟨u, rfl⟩
    refine ⟨key u, ?_⟩
    rw [← map_inv]
    exact key u⁻¹
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, h2 i j⟩
    have hinj : Function.Injective (RingHom.mapMatrix S.subtype :
        Matrix (Fin n) (Fin n) S →+* Matrix (Fin n) (Fin n) L) :=
      Matrix.map_injective Subtype.val_injective
    have hM : RingHom.mapMatrix S.subtype M = (g : Matrix (Fin n) (Fin n) L) := by
      ext i j; rfl
    have hN : RingHom.mapMatrix S.subtype N = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      ext i j; rfl
    refine ⟨⟨M, N, hinj ?_, hinj ?_⟩, Units.ext hM⟩
    · rw [map_mul, hM, hN, map_one]; exact Units.mul_inv g
    · rw [map_mul, hM, hN, map_one]; exact Units.inv_mul g

end Sub

theorem glMap_std_eq_iff_mem_GLint (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      g ∈ GLint (Fin n) (Ov E w) := by
  rw [glMap_std_eq_iff_entry, mem_GLint_iff_entry]
  have key : ∀ x : w.adicCompletion E,
      (∃ a : w.adicCompletionIntegers E,
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a = x) ↔ x ∈ Ov E w :=
    fun x => ⟨fun ⟨a, ha⟩ => ha ▸ a.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simp only [key]

end GlobalTheory.LatHecke
