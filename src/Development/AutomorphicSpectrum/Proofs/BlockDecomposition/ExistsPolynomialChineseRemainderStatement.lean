module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolynomialChineseRemainder
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

theorem _root_.GlobalTheory.T.exists_polynomial_chinese_remainder : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ g : ∀ (r : ℕ) (Q : SelfRecip E r), Fld Q, ∃ m : E[X], ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → (AdjoinRoot.mk Q.1 m : Fld Q) = g r Q := by
  first | exact @GlobalTheory.CompanionTheory.EllCRT.main | exact GlobalTheory.CompanionTheory.EllCRT.main | (intros; apply GlobalTheory.CompanionTheory.EllCRT.main <;> assumption)
