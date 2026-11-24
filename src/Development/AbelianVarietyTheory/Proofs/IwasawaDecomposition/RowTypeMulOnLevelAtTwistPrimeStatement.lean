module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowTypeMulOnLevelAtTwistPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.rowType_mul_on_level_at_twistPrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ g ∈ Jat (Pr := Pr) (R := R) sharp j P, ∀ g' ∈ Jat (Pr := Pr) (R := R) sharp j P, lamRow Ch mu sharp j P (g * g').toLinearMap = lamRow Ch mu sharp j P g.toLinearMap * lamRow Ch mu sharp j P g'.toLinearMap := by
  first | exact @GlobalTheory.TwistRowMul.lamRow_mul | exact GlobalTheory.TwistRowMul.lamRow_mul | (intros; apply GlobalTheory.TwistRowMul.lamRow_mul <;> assumption)
