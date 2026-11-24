module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterStepZeroTypePrime
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

theorem _root_.GlobalTheory.T.levelCharacter_stepZero_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → (∀ a : X.E, IntAt P.1 a → cst.psi P (a / (qOf P.1 : X.E)) = psi0P Ch P.1 (redP P.1 a)) → ChrG Ch sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  first | exact @GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero | exact GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero | (intros; apply GlobalTheory.Proof.levelCharacter_stepZero_typePrime.chrG_zero <;> assumption)
