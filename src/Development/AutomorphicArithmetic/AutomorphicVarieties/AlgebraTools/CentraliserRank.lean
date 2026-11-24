module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagNeZero
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff

@[expose] public section

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.centraliser_rank :
    ∀ {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → F) (P : Matrix ι ι F), Function.Injective a → P.charpoly = ∏ i, (X - C (a i)) → Module.finrank F (LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P)) = Fintype.card ι ∧ ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
  intro F _ ι _ _ a P ha hP
  have hu : ∀ i j, i ≠ j → IsUnit (a i - a j) := fun i j hij =>
    (sub_ne_zero.2 (fun h => hij (ha h))).isUnit
  have hCH : aeval P (∏ i, (X - C (a i))) = 0 := by
    rw [← hP]; exact Matrix.aeval_self_charpoly P
  obtain ⟨hcoi, -, -, hcomm⟩ := UpperTheory.V.AlgebraTools.lag_coi a P hu hCH
  have hne := UpperTheory.V.AlgebraTools.lag_ne_zero a P hu (by
    rw [hP, Polynomial.map_prod]; simp)
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ hcoi hne
  have hpoly : ∀ i, ∃ q : F[X], UpperTheory.V.AlgebraTools.lag a P i = aeval P q := fun i =>
    ⟨_ • _, by rw [UpperTheory.V.AlgebraTools.lag, map_smul]⟩
  set f := UpperTheory.V.AlgebraTools.lag a P with hf
  have hinj : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      (g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F) → A = B := by
    intro A B h
    exact (Units.mul_right_inj g).1 ((Units.mul_left_inj g⁻¹).1 h)
  have hmul : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * (A * B) * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      ((g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F)) *
      ((g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F)) := by
    intro A B
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  have hspan : ∀ Y, P * Y = Y * P → ∃ c : ι → F, Y = ∑ i, c i • f i := by
    intro Y hY
    set Z := (g : Matrix ι ι F) * Y * ((g⁻¹ : GL ι F) : Matrix ι ι F) with hZ
    refine ⟨fun i => Z i i, hinj _ _ ?_⟩
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
    rw [← hZ]
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · have h1 : Z * single j j (1 : F) = single j j 1 * Z := by
          rw [← hg j, hZ, ← hmul, ← hmul, (hcomm Y j hY.symm).eq]
        have h2 := congrFun (congrFun h1 i) j
        rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h2
        rw [mul_one] at h2
        simp [hij, h2]
    · intro b _ hb
      simp [hb]
    · simp
  have hq : ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
    intro Y hY
    obtain ⟨c, rfl⟩ := hspan Y hY
    choose q hq using hpoly
    exact ⟨∑ i, c i • q i, by simp [hq]⟩
  refine ⟨?_, hq⟩
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 : (∑ i, c i • f i) * f j = c j • f j := by
      rw [Finset.sum_mul, Finset.sum_eq_single j]
      · rw [smul_mul_assoc, (hcoi.idem j).eq]
      · intro b _ hb
        rw [smul_mul_assoc, hcoi.ortho hb, smul_zero]
      · simp
    rw [hc, zero_mul] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_right (hne j)
  have hker : LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P) =
      Submodule.span F (Set.range f) := by
    apply le_antisymm
    · intro Y hY
      have hY' : P * Y = Y * P := by simpa [sub_eq_zero] using hY
      obtain ⟨c, rfl⟩ := hspan Y hY'
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := (hcomm P i (Commute.refl P)).eq
      simpa [sub_eq_zero] using this
  rw [hker, finrank_span_eq_card hli]
