module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZero
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

theorem _root_.GlobalTheory.T.double_complex_lead_zero_of_class_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | exact GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero <;> assumption)
