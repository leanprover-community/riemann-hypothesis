module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.BlockHomomorphism

noncomputable def IsSmooth : {k G V : Type} →
  [inst : Field k] →
    [inst_1 : Group G] →
      [inst_2 : AddCommGroup V] → [inst_3 : Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
  fun {k G V} [Field k] [Group G] [AddCommGroup V] [Module k V] [TopologicalSpace G] ρ =>
    ∀ (v : V), IsOpen {g | (ρ g) v = v}

noncomputable def glCongr : (k : Type) →
  [inst : Field k] → {a b : ℕ} → a = b → GL (Fin a) k →* GL (Fin b) k :=
  fun k [Field k] {a b} h => Units.map (Matrix.reindexAlgEquiv k k (finCongr h)).toMulEquiv.toMonoidHom

theorem aux3 : ∀ (k : Type) [inst : Field k] (n r : ℕ),
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0
    (1 : Matrix (Fin r) (Fin r) k) = 1 := by
  intro k _ n r
  exact Matrix.fromBlocks_one

theorem aux4 : ∀ (k : Type) [inst : Field k] (n r : ℕ)
  (A B : Matrix (Fin n) (Fin n) k),
  Matrix.fromBlocks (A * B) 0 0 (1 : Matrix (Fin r) (Fin r) k) =
    Matrix.fromBlocks A 0 0 1 * Matrix.fromBlocks B 0 0 1 := by
  intro k _ n r A B
  simp [Matrix.fromBlocks_multiply]

noncomputable def blkHom : (k : Type) →
  [inst : Field k] → (n r : ℕ) → Matrix (Fin n) (Fin n) k →* Matrix (Fin n ⊕ Fin r) (Fin n ⊕ Fin r) k :=
  fun k [Field k] n r =>
    { toFun := fun A => Matrix.fromBlocks A 0 0 1, map_one' := aux3 k n r,
      map_mul' := aux4 k n r }

noncomputable def blkGL : (k : Type) →
  [inst : Field k] → (n r : ℕ) → GL (Fin n) k →* GL (Fin (n + r)) k :=
  fun k [Field k] n r =>
    Units.map
      ((Matrix.reindexAlgEquiv k k finSumFinEquiv).toMulEquiv.toMonoidHom.comp
        (blkHom k n r))

noncomputable def blkAt : (k : Type) →
  [inst : Field k] → (n N : ℕ) → n ≤ N → GL (Fin n) k →* GL (Fin N) k :=
  fun k [Field k] n N h =>
    (glCongr k (Nat.add_sub_cancel' h)).comp
      (blkGL k n (N - n))

noncomputable def FixK : {k : Type} →
  [inst : Field k] →
    {m N : ℕ} →
      m + 1 ≤ N →
        {V : Type} →
          [inst_1 : AddCommGroup V] →
            [inst_2 : Module ℂ V] → Representation ℂ (GL (Fin N) k) V → Subgroup (GL (Fin (m + 1)) k) → V → Prop :=
  fun {k} [Field k] {m N} h {V} [AddCommGroup V] [Module ℂ V] π K v =>
    ∀ g ∈ K, (π ((blkAt k (m + 1) N h) g)) v = v

theorem aux9 : ∀ {m N : ℕ} {h : m + 2 ≤ N}, ¬m + 1 ≤ N → False := by
  intro m N h a
  omega

private theorem continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have h1 : Continuous (blkGL k n (N - n)) := by
    unfold blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (glCongr k e) := by
    intro a b e
    unfold glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1

private def fixer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_fixK : ∀ {k : Type} [inst : Field k]
  [inst_1 : ValuativeRel k] [inst_2 : TopologicalSpace k] [IsNonarchimedeanLocalField k] {m N : ℕ} {h : m + 2 ≤ N}
  {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V},
  IsSmooth π →
    ∀ (v w : V),
      ∃ K : Subgroup (GL (Fin (m + 1)) k),
        IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧
          FixK
              (Decidable.byContradiction fun a => aux9 (h := h) a) π K v ∧
            FixK
              (Decidable.byContradiction fun a => aux9 (h := h) a) π K w := by
  intro k _ _ _ _ m N h V _ _ π hπ v w
  have hle : m + 1 ≤ N := by omega
  refine ⟨(fixer π v ⊓ fixer π w).comap
    (blkAt k (m + 1) N hle), ?_, fun g hg => hg.1, fun g hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (continuous_blkAt (m + 1) N hle)

end UpperTheory.Reformulated.B.BlockHomomorphism
