module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

open Matrix Polynomial

namespace GlobalTheory

theorem irreducible_dvd_of_dvd_charpoly_of_aeval_matrix {K : Type} [Field K] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) K) (p q : K[X]) (hp : Irreducible p)
    (hd : p ∣ M.charpoly) (hq : aeval M q = 0) : p ∣ q := by
  classical
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let M' := M.map (algebraMap K L)
  have hM' : aeval M' q = 0 := by
    have := Polynomial.aeval_algHom_apply ((Algebra.ofId K L).mapMatrix (m := Fin h)) M q
    rw [hq, map_zero] at this
    exact this
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (q.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap, hM'] at h2
  have hnt : Nontrivial (Matrix (Fin h) (Fin h) L) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (spectrum.mem_iff.1 hs) (isUnit_of_subsingleton _)
  rw [spectrum.zero_eq, Set.mem_singleton_iff] at h2
  simp only [eval_map, ← aeval_def] at h2
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  exact h2

theorem charpoly_eq_pow_of_aeval_irreducible_eq_zero :
    ∀ (K : Type) [Field K] (h N : ℕ) (M : Matrix (Fin h) (Fin h) K) (f : K[X]), f.Monic →
      Irreducible f → Polynomial.aeval M f = 0 → h = f.natDegree * N → M.charpoly = f ^ N := by
  intro K _ h N M f hfm hfi hf hh
  classical
  have hc0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hmem : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors M.charpoly, b = f := by
    intro b hb
    have hbi := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb
    have hbd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
    have hbn := UniqueFactorizationMonoid.normalize_normalized_factor b hb
    have hbm : b.Monic := by
      rw [← hbn]; exact Polynomial.monic_normalize hbi.ne_zero
    have hbf := irreducible_dvd_of_dvd_charpoly_of_aeval_matrix M b f hbi hbd hf
    exact eq_of_monic_of_associated hbm hfm (hbi.associated_of_dvd hfi hbf)
  set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors M.charpoly)
  have hrep : UniqueFactorizationMonoid.normalizedFactors M.charpoly = Multiset.replicate n f :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hass := UniqueFactorizationMonoid.prod_normalizedFactors hc0
  rw [hrep, Multiset.prod_replicate] at hass
  have hcp : M.charpoly = f ^ n :=
    (eq_of_monic_of_associated (hfm.pow n) (Matrix.charpoly_monic M) hass).symm
  have hdeg : f.natDegree * n = f.natDegree * N := by
    have := congrArg Polynomial.natDegree hcp
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hfm.natDegree_pow] at this
    rw [← hh]; linarith
  have hpos : 0 < f.natDegree := Irreducible.natDegree_pos hfi
  rw [hcp, Nat.eq_of_mul_eq_mul_left hpos hdeg]

end GlobalTheory
