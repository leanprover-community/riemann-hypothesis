module

import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.CosetCover
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SemilocalBasis

open scoped Pointwise

theorem exists_forall_notMem {A V J : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [AddCommGroup V] [Module A V] [Finite J]
    (p : J → Submodule A V) (hp : ∀ i, p i ≠ ⊤)
    (hm : ∀ i, ∀ a ∈ IsLocalRing.maximalIdeal A, ∀ x, a • x ∈ p i) : ∃ x : V, ∀ i, x ∉ p i := by
  let I := IsLocalRing.maximalIdeal A
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : Infinite (A ⧸ I) := inferInstanceAs (Infinite (IsLocalRing.ResidueField A))
  let N : Submodule A V := I • ⊤
  let q : V →ₛₗ[Ideal.Quotient.mk I] V ⧸ N :=
    { toFun := Submodule.Quotient.mk
      map_add' := map_add N.mkQ
      map_smul' := Module.Quotient.mk_smul_mk V I }
  have hq : LinearMap.ker q = N := Submodule.ker_mkQ N
  have hle (i : J) : N ≤ p i := Submodule.smul_le.mpr fun a ha x _ => hm i a ha x
  have hne (i : J) : (p i).map q ≠ ⊤ := by
    intro h
    have hc := Submodule.comap_map_eq_self (f := q) (hq ▸ hle i)
    rw [h, Submodule.comap_top] at hc
    exact hp i hc.symm
  obtain ⟨y, hy⟩ := Submodule.exists_forall_notMem_of_forall_ne_top (K := A ⧸ I) (fun i => (p i).map q) hne
  obtain ⟨x, rfl⟩ := N.mkQ_surjective y
  exact ⟨x, fun i hx => hy i (Submodule.mem_map_of_mem hx)⟩

noncomputable def red {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : M →ₗ[B] (Fin n → B ⧸ I) :=
  LinearMap.pi fun j => (Submodule.mkQ I).comp (e.coord j)

theorem red_apply {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) (x : M) (j : Fin n) :
    red e I x j = Ideal.Quotient.mk I (e.repr x j) := rfl

theorem red_surjective {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M] {n : ℕ}
    (e : Module.Basis (Fin n) B M) (I : Ideal B) : Function.Surjective (red e I) := by
  intro y
  choose s hs using Ideal.Quotient.mk_surjective (I := I)
  refine ⟨e.equivFun.symm fun j => s (y j), ?_⟩
  ext j
  rw [red_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, hs]

theorem exists_linearIndependent {A B M : Type*} [CommRing A] [IsLocalRing A]
    [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B]
    [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    {n : ℕ} (e : Module.Basis (Fin n) B M) (N : Submodule A M)
    (hm : ∀ m : MaximalSpectrum B,
      (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal)
    (hN : Submodule.span B (N : Set M) = ⊤) (k : ℕ) (hk : k ≤ n) :
    ∃ v : Fin k → M, (∀ i, v i ∈ N) ∧ ∀ m : MaximalSpectrum B,
      LinearIndependent (B ⧸ m.asIdeal) (fun i => red e m.asIdeal (v i)) := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun _ => linearIndependent_empty_type⟩
  | succ k ih =>
    obtain ⟨v, hvN, hv⟩ := ih (by omega)
    let W : ∀ m : MaximalSpectrum B, Submodule (B ⧸ m.asIdeal) (Fin n → B ⧸ m.asIdeal) :=
      fun m => Submodule.span _ (Set.range fun i => red e m.asIdeal (v i))
    let q : MaximalSpectrum B → Submodule B M :=
      fun m => ((W m).restrictScalars B).comap (red e m.asIdeal)
    let p : MaximalSpectrum B → Submodule A N :=
      fun m => ((q m).restrictScalars A).comap N.subtype
    obtain ⟨x, hx⟩ := exists_forall_notMem p (fun m h => by
      have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : q m = ⊤ := by
        rw [eq_top_iff, ← hN, Submodule.span_le]
        intro y hy
        have : (⟨y, hy⟩ : N) ∈ p m := h ▸ Submodule.mem_top
        exact this
      have h2 : W m = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨z, rfl⟩ := red_surjective e m.asIdeal y
        have : z ∈ q m := h1 ▸ Submodule.mem_top
        exact this
      have h3 : Module.finrank (B ⧸ m.asIdeal) (W m) = k := by
        have := finrank_span_eq_card (hv m)
        simpa using this
      rw [h2] at h3
      simp at h3
      omega) (fun m a ha y => by
      have h0 : red e m.asIdeal (a • (y : M)) = 0 := by
        ext j
        rw [red_apply, ← algebraMap_smul B, map_smul, Finsupp.smul_apply, smul_eq_mul,
          Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mul_mem_right _ _ (hm m (Ideal.mem_map_of_mem _ ha))
      change red e m.asIdeal (a • (y : M)) ∈ W m
      rw [h0]
      exact zero_mem _)
    refine ⟨Fin.cons (x : M) v, fun i => ?_, fun m => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact x.2
      · exact hvN j
    · have := m.isMaximal
      letI := Ideal.Quotient.field m.asIdeal
      have h1 : (fun i => red e m.asIdeal (Fin.cons (α := fun _ => M) (x : M) v i)) =
          Fin.cons (red e m.asIdeal x) (fun i => red e m.asIdeal (v i)) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      rw [h1, linearIndependent_finCons]
      exact ⟨hv m, hx m⟩

end SemilocalBasis

theorem exists_basis_mem_of_span_eq_top_of_semilocal :
    ∀ (A B M : Type) [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] (n : ℕ) (_ : Module.Basis (Fin n) B M) (N : Submodule A M), (∀ m : MaximalSpectrum B, (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal) → Submodule.span B (N : Set M) = ⊤ → ∃ b : Module.Basis (Fin n) B M, ∀ i, b i ∈ N := by
  intro A B M _ _ _ _ _ _ _ _ _ _ n e N hm hN
  obtain ⟨v, hvN, hv⟩ := SemilocalBasis.exists_linearIndependent e N hm hN n le_rfl
  have hu : IsUnit (e.det v) := by
    by_contra hne
    obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hne
    letI := Ideal.Quotient.field I
    have h1 := hv ⟨I, hI⟩
    have h2 : IsUnit ((e.toMatrix v).map (Ideal.Quotient.mk I)) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp h1
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Module.Basis.det_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at h2
    exact not_isUnit_zero h2
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr hu
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simpa using hvN i⟩

end GlobalTheory
