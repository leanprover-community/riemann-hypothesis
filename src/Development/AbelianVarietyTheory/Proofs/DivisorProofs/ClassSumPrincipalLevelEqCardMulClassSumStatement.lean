module

public import Formalism.LocalToGlobal.Columns.ToHLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumPrincipalLevelEqCardMulClassSum
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
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_card_mul_classSum : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs) (hX : X.Ok) (v : InfinitePlace X.K) (F' : (mtildeKGSD W Ch sel mu).EqFun), F'.1 ∈ (mtildeGSD W Ch sel mu P).EqFun → (mtildeKGSD W Ch sel mu).ipAt (mtildeKOk W Ch sel mu hX) v F'.1 F'.1 = (Nat.card P.grp : ℂ) * (mtildeGSD W Ch sel mu P).ipAt (mtildeOk W Ch sel mu hX P) v F'.1 F'.1 := by
  first | exact @GlobalTheory.change_of_level_classSum | exact GlobalTheory.change_of_level_classSum | (intros; apply GlobalTheory.change_of_level_classSum <;> assumption)
