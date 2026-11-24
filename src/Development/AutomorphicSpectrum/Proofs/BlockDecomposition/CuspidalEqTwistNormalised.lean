module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.UnitaryBC PositivityTheory.PRW.GKD

namespace GlobalTheory.CompanionTheory.TwistNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem val_expId (ω : HChar E) (t : ℝ) :
    ((ω.1 (GlobalTheory.DiscChar.expId E t) : ℂˣ) : ℂ) = Complex.exp (t * dchi ω 1) := by
  refine (chiInf_expU ω _).trans (congrArg _ ?_)
  rw [show (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) from funext fun _ => by simp, map_smul]
  simp

theorem isNormalised_rank_zero (π : CuspSub E 0) : IsNormalised π := fun φ _ t g => by
  rw [Subsingleton.elim (splitCentre E 0 t * g) g]

theorem isNormalised_twist {π : CuspSub E a} {ω ν : HChar E} (hω : π.HasCentral ω)
    (hν : ∀ t : ℝ, ((chiDet a ν (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (-(t * dchi ω 1))) :
    IsNormalised (π.twist ν) := by
  rintro _ ⟨ψ, hψ, rfl⟩ t g
  change ψ.1 (splitCentre E a t * g) * (chiDet a ν (splitCentre E a t * g) : ℂˣ) = ψ.1 g * (chiDet a ν g : ℂˣ)
  have h1 : ψ.1 (splitCentre E a t * g) = Complex.exp (t * dchi ω 1) * ψ.1 g := by
    rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar, hω.apply hψ]
    exact congrArg (· * ψ.1 g) (val_expId ω t)
  rw [h1, map_mul, Units.val_mul, hν, mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem exists_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a),
    ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  intro E _ _ _ a π
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨π, 1, isNormalised_rank_zero π, π.twist_one.symm⟩
  · obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
    refine ⟨π.twist ν, ν⁻¹, isNormalised_twist hω hν, ?_⟩
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]

end GlobalTheory.CompanionTheory.TwistNorm

end
