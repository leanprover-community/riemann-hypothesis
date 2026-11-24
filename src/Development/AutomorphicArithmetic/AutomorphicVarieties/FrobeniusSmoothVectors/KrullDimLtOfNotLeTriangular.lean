module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyCoeffsInSubalgebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TameInertiaCondition
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
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_le_of_primes {A : Type} [CommRing A] (I : Ideal A) (c : WithBot ℕ∞)
    (h : ∀ P : Ideal A, P.IsPrime → I ≤ P → ringKrullDim (A ⧸ P) ≤ c) : ringKrullDim (A ⧸ I) ≤ c := by
  rw [ringKrullDim_quotient]
  refine iSup_le fun s => ?_
  refine le_trans ?_ (h s.head.1.asIdeal s.head.1.isPrime s.head.2)
  rw [ringKrullDim_quotient]
  let t : LTSeries (PrimeSpectrum.zeroLocus (R := A) s.head.1.asIdeal) :=
    ⟨s.length, fun i => ⟨(s i).1, (show s.head.1 ≤ (s i).1 from s.head_le i)⟩, fun i => s.step i⟩
  exact Order.LTSeries.length_le_krullDim t

private theorem dim_anti {A : Type} [CommRing A] {I J : Ideal A} (h : I ≤ J) :
    ringKrullDim (A ⧸ J) ≤ ringKrullDim (A ⧸ I) :=
  ringKrullDim_le_of_surjective (Ideal.Quotient.factor h) (Ideal.Quotient.factor_surjective h)

private theorem le_of_add_le {a : WithBot ℕ∞} {b c m : ℕ} (h : a + b ≤ (c : ℕ)) (hm : c ≤ m + b) :
    a ≤ (m : ℕ) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (⊤ : ℕ∞) + (b : ℕ∞) ≤ (c : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe a =>
      have h' : a + b ≤ c := by exact_mod_cast h
      have : a ≤ m := by omega
      exact_mod_cast this

theorem UpperTheory.V.Fr.krull_dim_lt_of_not_le_triangular :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), F.Big C₀ → ¬ S.u.triP ≤ x → ringKrullDim (L.R ⧸ L.ρ.triM) < (n * F.d : ℕ) ∧ ∀ I : Ideal S.B, S.FinLam I → ∀ v i j, i ≠ j → ringKrullDim (L.R ⧸ (I.map L.b ⊔ (maximalIdeal O).map (algebraMap O L.R) ⊔ Ideal.span {y | ∃ g ∈ F.Nv v, y = (L.ρ.ψ v i g : L.R) - L.ρ.ψ v j g})) < (n * F.d : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L hB hx
  obtain ⟨h1, h2⟩ := l51 hF hn S x L hx
  obtain ⟨hd, hdv⟩ := hB
  have hlt : ((n * F.d - 1 : ℕ) : WithBot ℕ∞) < (n * F.d : ℕ) := by
    have : n * F.d - 1 < n * F.d := by rcases hn with rfl | rfl <;> omega
    exact_mod_cast this
  have hT : ringKrullDim (L.R ⧸ L.ρ.triM) ≤ (n * F.d - 1 : ℕ) := by
    refine h1.trans ?_
    have : (n - 1) * F.d + 2 + (3 * C₀ + 5) ≤ n * F.d - 1 := by rcases hn with rfl | rfl <;> omega
    exact_mod_cast this
  refine ⟨hT.trans_lt hlt, fun I hI v i j hij => lt_of_le_of_lt (dim_le_of_primes _ _ fun P hP hle => ?_) hlt⟩
  by_cases hM : L.ρ.triM ≤ P
  · exact (dim_anti hM).trans hT
  have hoff : L.ρ.OffTri P := ⟨fun h => hP.ne_top (top_le_iff.1 (h2 ▸ h)), hM⟩
  have hIP : I ≤ L.π P :=
    (Ideal.map_le_iff_le_comap (f := L.b)).1 (le_sup_left.trans (le_sup_left.trans hle))
  have hco : L.ρ.Coin P v i j := fun g hg => (le_sup_right.trans hle) (Ideal.subset_span ⟨g, hg, rfl⟩)
  have h := (l52 hF hn S x L I hI v i j hij P hP hoff hIP hco).2 (le_sup_right.trans (le_sup_left.trans hle))
  refine le_of_add_le h ?_
  have := hdv v
  rcases hn with rfl | rfl <;> omega
