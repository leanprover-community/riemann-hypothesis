module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

noncomputable section
namespace GlobalTheory.ColFourier

theorem fourier_pi_inversion_at {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type*} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} {c : kˣ} {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) (a : n → k) :
    ∫ y : n → k, (∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)
      ∂(Measure.pi fun _ => ν) = g a := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hh : (fun x => g (x + a)) ∈ SB (n → k) :=
    ⟨hg.1.comp_continuous (by fun_prop), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have h1 := (FourierPi.fourier_pi_of_conductor h hν hh).2
  simp only [zero_add] at h1
  rw [← h1]
  congr 1
  funext y
  rw [← integral_mul_const,
    ← integral_add_right_eq_self (fun x => g x * (ψ (x ⬝ᵥ y) : ℂ) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)) a]
  congr 1
  funext x
  rw [add_dotProduct, AddChar.map_add_eq_mul, AddChar.inv_apply', dotProduct_comm y a, mul_assoc,
    ← Circle.coe_mul, mul_inv_cancel_right]

theorem fourierInt_inv_fourierInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  have hν : IsSelfDual ψ m := isSelfDual_of_isUnitVol m hψ hm
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  funext X
  have h0 := comp_setCols_mem_SB hΞ P X
  have hg : (fun x : (_ : A) × P → k => Ξ (setCols P X (Matrix.of fun i j => x ⟨i, j⟩))) ∈
      SB ((_ : A) × P → k) :=
    ⟨h0.1.comp_continuous (f := fun x : (_ : A) × P → k => (Matrix.of fun i j => x ⟨i, j⟩ : Matrix A P k))
        (continuous_pi fun i => continuous_pi fun j => continuous_apply _),
      HasCompactSupport.intro (h0.2.image (f := fun (U : Matrix A P k) (p : (_ : A) × P) => U p.1 p.2)
        (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
        fun x hx => image_eq_zero_of_notMem_tsupport (f := fun U => Ξ (setCols P X U)) fun h => hx ⟨_, h, rfl⟩⟩
  have h1 := fourier_pi_inversion_at hψ hν hg (fun p => X p.1 p.2)
  have h2 : setCols P X (Matrix.of fun i (j : P) => X i j) = X := setCols_restrictCols P X
  simp only [h2] at h1
  rw [← h1, fourierInt_eq_pi]
  congr 1
  funext y
  rw [fourierInt_eq_pi]
  have h3 : (fun p : (_ : A) × P => setCols P X (Matrix.of fun i j => y ⟨i, j⟩) p.1 p.2) = y := by
    funext p
    simp [setCols, p.2.2]
  simp only [setCols_setCols, h3]

end GlobalTheory.ColFourier
