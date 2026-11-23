module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZeroStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem row_iso_of_columns : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  intro R _ K a hK j
  have hab : ∀ p q, a < q → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_gt h)
  have hbe : ∀ p q, q < a → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_lt h)
  have hs := GlobalTheory.T.double_complex_class_surjective K a j hab
  have hk := GlobalTheory.T.double_complex_lead_zero_of_class_zero K a j hab
  have hi := GlobalTheory.T.double_complex_class_zero_of_lead_zero K a j hbe
  have hl := GlobalTheory.T.double_complex_lead_surjective K a j hbe
  let c := clsZ K (a + j) j
  let ψ : Zf K (a + j) j →ₗ[R] (colH K a).H j := leadE K j a
  have hle : LinearMap.ker c ≤ LinearMap.ker ψ := fun z hz => hk z hz
  let L := (LinearMap.ker c).liftQ ψ hle
  have hL : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun x hx => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      have hz : ψ z = 0 := by simpa [L] using hx
      have hc : c z = 0 := hi z hz
      exact (Submodule.Quotient.mk_eq_zero _).2 hc
    · intro y
      obtain ⟨z, rfl⟩ := hl y
      exact ⟨Submodule.Quotient.mk z, Submodule.liftQ_apply _ _ _⟩
  let e0 := c.quotKerEquivOfSurjective hs
  refine ⟨e0.symm.trans (LinearEquiv.ofBijective L hL), fun z => ?_⟩
  have h0 : e0.symm (c z) = Submodule.Quotient.mk z :=
    e0.symm_apply_eq.2 (LinearMap.quotKerEquivOfSurjective_apply_mk c hs z).symm
  change L (e0.symm (c z)) = ψ z
  rw [h0]
  exact Submodule.liftQ_apply _ _ _

end GlobalTheory.CompanionTheory.CechSerre
