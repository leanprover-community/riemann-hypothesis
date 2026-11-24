module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CoiConjSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagNeZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagTriangular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.OrdExt
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

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem entry_of_conj {C : Type} [CommRing C] {n : ℕ} (g : GL (Fin n) C) (f : Fin n → Matrix (Fin n) (Fin n) C)
    (hg : ∀ i, (g : Matrix (Fin n) (Fin n) C) * f i * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) = single i i 1)
    (M : Matrix (Fin n) (Fin n) C) (a b : Fin n) :
    ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b =
      ((g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) a b := by
  have h : (g : Matrix (Fin n) (Fin n) C) * (f a * M * f b) * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      single a a 1 * ((g : Matrix (Fin n) (Fin n) C) * M * ((g⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C)) *
        single b b 1 := by
    rw [← hg a, ← hg b]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [h, Matrix.mul_single_apply_same, Matrix.single_mul_apply_same, one_mul, mul_one]

theorem UpperTheory.V.Fr.flag_loc :
    ∀ {H C : Type} [Group H] [CommRing C] [IsLocalRing C] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) C) (ψ : Fin n → H →* Cˣ) (g₀ : H), (∀ i j, i ≠ j → IsUnit ((ψ i g₀ : C) - ψ j g₀)) → ((r g₀).map (residue C)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (residue C (ψ i g₀))) → (∀ g, ordProd r (fun i s => (ψ i s : C)) g = 0) → UpperTheory.V.W.HasFlag r.toHomUnits ψ := by
  intro H C _ _ _ n r ψ g₀ hu hc ho
  have h0 := UpperTheory.V.AlgebraTools.ord_ext (R := C) r (fun i => (Units.coeHom C).comp (ψ i)) (fun g => by
    have := ho g
    unfold ordProd at this
    simpa only [Algebra.algebraMap_eq_smul_one, MonoidHom.comp_apply, Units.coeHom_apply] using this)
  obtain ⟨h1, h2, h3⟩ := UpperTheory.V.AlgebraTools.lag_triangular (MonoidAlgebra.lift C (Matrix (Fin n) (Fin n) C) H r)
    (fun i => MonoidAlgebra.lift C C H ((Units.coeHom C).comp (ψ i))) (MonoidAlgebra.of C H g₀) h0
    (fun i j hij => by simpa using hu i j hij)
  simp only [MonoidAlgebra.lift_of, MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 h3
  have h4 := UpperTheory.V.AlgebraTools.lag_ne_zero (fun i => (ψ i g₀ : C)) (r g₀) hu (by rw [← Matrix.charpoly_map, hc])
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ h1 h4
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have h5 := h2 (MonoidAlgebra.of C H s) i j hij
    rw [MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i j
    rw [h5, mul_zero, zero_mul] at h6
    exact h6
  · have h5 := h3 (MonoidAlgebra.of C H s) i
    rw [MonoidAlgebra.lift_of, MonoidAlgebra.lift_of] at h5
    have h6 := entry_of_conj g _ hg (r s) i i
    rw [h5, mul_smul_comm, smul_mul_assoc, hg] at h6
    refine h6.trans ?_
    simp
