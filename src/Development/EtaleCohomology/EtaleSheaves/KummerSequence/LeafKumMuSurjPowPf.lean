module

public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf

namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf

def powCof {A : Type*} [CommRing A] (u v : A) (q : ℕ) : A := ∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)

theorem powCof_mul {A : Type*} [CommRing A] (u v : A) (q : ℕ) : powCof u v q * (u - v) = u ^ q - v ^ q :=
  geom_sum₂_mul u v q

theorem powCof_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (u v : A) (q : ℕ) :
    φ (powCof u v q) = powCof (φ u) (φ v) q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [powCof, map_sum, map_mul, map_pow]

theorem powCof_self {A : Type*} [CommRing A] (v : A) (q : ℕ) : powCof v v q = (q : A) * v ^ (q - 1) := by
  unfold powCof
  rw [Finset.sum_congr rfl (g := fun _ => v ^ (q - 1))]
  · simp
  · intro i hi
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega

theorem field_step {K : Type} [Field K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z w : K)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) (hw : w ^ q = 1) :
    ∃ a : Fin q, powCof w (z ^ (a : ℕ)) q ≠ 0 := by
  have : NeZero (q : K) := ⟨hq⟩
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic q K) z := by
    rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Polynomial.eval_map]
    rw [Polynomial.aeval_def, algebraMap_int_eq] at hz
    exact hz
  have hp : IsPrimitiveRoot z q := (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨i, hi, hzi⟩ := hp.eq_pow_of_pow_eq_one hw
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [← hzi, powCof_self]
  have hz0 : z ≠ 0 := fun h => by
    have := hp.pow_eq_one; rw [h, zero_pow (NeZero.ne q)] at this; exact zero_ne_one this
  exact mul_ne_zero hq (pow_ne_zero _ (pow_ne_zero _ hz0))

theorem isUnit_of_basicOpen_top {V : Scheme.{0}} (t : Γ(V, ⊤)) (h : V.basicOpen t = ⊤) : IsUnit t := by
  apply V.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ V.basicOpen t := by rw [h]; trivial
  exact (V.mem_basicOpen_top t x).1 hx'

theorem pow_pf : LeafKumMuSurjPow := by
  intro q _ U ζ u hu
  let s : Fin q → Γ(U, ⊤) := fun a => powCof (u : Γ(U, ⊤)) (ζ.1 ^ (a : ℕ)) q
  have hcov : TopologicalSpace.IsOpenCover (fun a => U.basicOpen (s a)) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    let φ := (U.Γevaluation x).hom
    have hq : (q : U.residueField x) ≠ 0 := by
      have := ζ.2.1.map φ
      simpa using this.ne_zero
    have hz : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by
      have := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
      rw [ζ.2.2, map_zero] at this
      exact this
    have hw : (φ (u : Γ(U, ⊤))) ^ q = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
    obtain ⟨a, ha⟩ := field_step q hq _ _ hz hw
    refine ⟨a, ?_⟩
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x trivial]
    show φ (s a) ≠ 0
    simp only [s]
    rw [powCof_map, map_pow]
    exact ha
  let 𝒰 := U.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰), ?_⟩
  intro V f hf
  obtain ⟨a', g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  let a : Fin q := a'
  refine ⟨(a : ℕ), ?_⟩
  have hunit : IsUnit ((g ≫ 𝒰.f a).appTop (s a)) := by
    apply isUnit_of_basicOpen_top
    rw [← Scheme.preimage_basicOpen_top, eq_top_iff]
    intro x _
    show (U.basicOpen (s a)).ι.base (g.base x) ∈ U.basicOpen (s a)
    exact (g.base x).2
  have hzero : s a * ((u : Γ(U, ⊤)) - ζ.1 ^ (a : ℕ)) = 0 := by
    simp only [s]
    rw [powCof_mul, ← Units.val_pow_eq_pow_val, hu, Units.val_one, ← pow_mul, mul_comm, pow_mul,
      prim_pow_q ζ, one_pow, sub_self]
  have key : ∀ ψ : Γ(U, ⊤) →+* Γ(V, ⊤), IsUnit (ψ (s a)) → ψ u = ψ ζ.1 ^ (a : ℕ) := fun ψ h => by
    have h2 := congrArg ψ hzero
    rw [map_mul, map_zero] at h2
    rw [← map_pow]
    exact sub_eq_zero.1 ((h.mul_right_eq_zero).1 (by rw [← map_sub]; exact h2))
  apply key
  exact hunit

theorem LeafKumMuSurjPow_of : LeafKumMuSurjPow := pow_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf
