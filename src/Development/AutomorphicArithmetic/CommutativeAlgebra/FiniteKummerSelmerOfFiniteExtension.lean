module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKernelPowClassesOfPrimitiveRoot
public import GroundTheory.FunctionField.PlaceAbove
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

@[expose] public section

open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem functionField_isAlgebraic_of_tower (k K K' : Type) [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
    [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] :
    Algebra.IsAlgebraic K K' := by
  have h := trdeg_add_eq k K (A := K')
  rw [trdeg_eq_one (k := k) (K := K), trdeg_eq_one (k := k) (K := K')] at h
  have hfin : Algebra.trdeg K K' < Cardinal.aleph0 :=
    lt_of_le_of_lt (h ▸ le_add_self) Cardinal.one_lt_aleph0
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hn] at h
  have hn0 : n = 0 := by
    have : ((1 + n : ℕ) : Cardinal) = ((1 : ℕ) : Cardinal) := by push_cast; exact h
    have := Nat.cast_injective this
    omega
  rw [← trdeg_eq_zero_iff, hn, hn0, Nat.cast_zero]

theorem UpperTheory.finite_kummerSelmer_of_finite_extension :
    ∀ (k K K' : Type) [Field k] [IsAlgClosed k] [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] [IsFunctionField k K] [IsFunctionField k K'] (q : ℕ) [NeZero q], IsUnit (q : k) → FinCls q (SelAll k K' q) → FinCls q (SelAll k K q) := by
  classical
  intro k K K' _ _ _ _ _ _ _ _ _ _ q _ hq hK'
  have := functionField_isAlgebraic_of_tower k K K'
  have : Algebra.EssFiniteType k K' := essFiniteType
  have : Algebra.EssFiniteType K K' := Algebra.EssFiniteType.of_comp k K K'
  have : Module.Finite K K' := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : NeZero (q : k) := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k q
  obtain ⟨T0, hT0⟩ := UpperTheory.finite_kernel_powClasses_of_primitive_root K K' q
    ⟨algebraMap k K ζ, hζ.map_of_injective (algebraMap k K).injective⟩
  obtain ⟨T', hT'⟩ := hK'
  let φ : Kˣ →* K'ˣ := Units.map (algebraMap K K' : K →* K')
  have hφ : ∀ x : Kˣ, ((φ x : K'ˣ) : K') = algebraMap K K' (x : K) := fun x => rfl
  have himg : ∀ f ∈ SelAll k K q, φ f ∈ SelAll k K' q := by
    intro f hf w
    have hw := (Place.liesOver_comap w).ord_algebraMap (f : K)
    show (q : ℤ) ∣ w.ord ((φ f : K'ˣ) : K')
    rw [hφ, hw]
    exact Dvd.dvd.mul_left (hf _) _
  let g : K'ˣ → Kˣ := fun t' =>
    if h : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q then h.choose else 1
  refine ⟨Finset.image₂ (· * ·) (T'.image g) T0, ?_⟩
  intro f hf
  obtain ⟨t', ht', u, hu⟩ := hT' (φ f) (himg f hf)
  have hex : ∃ f ∈ SelAll k K q, ∃ u : K'ˣ, φ f = t' * u ^ q := ⟨f, hf, u, hu⟩
  have hg : g t' = hex.choose := dif_pos hex
  obtain ⟨_, u0, hu0⟩ := hex.choose_spec
  set f0 := hex.choose
  have hmem : f * f0⁻¹ ∈ {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
    refine ⟨((u * u0⁻¹ : K'ˣ) : K'), ?_⟩
    rw [← hφ, map_mul, map_inv, hu, hu0]
    push_cast
    rw [mul_pow, inv_pow]
    field_simp
  obtain ⟨s, hs, w, hw⟩ := hT0 _ hmem
  refine ⟨f0 * s, Finset.mem_image₂.mpr ⟨f0, Finset.mem_image.mpr ⟨t', ht', hg⟩, s, hs, rfl⟩, w, ?_⟩
  rw [mul_assoc, ← hw, mul_comm f, mul_inv_cancel_left]
