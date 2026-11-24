module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GlobalTheory.CxCoh

theorem _root_.GlobalTheory.T.fourTermComplex_quasiIsoAt_formal_properties : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧ (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a := by
  first | exact @GlobalTheory.CxCoh.QAtFormal.qAt_formal | exact GlobalTheory.CxCoh.QAtFormal.qAt_formal | (intros; apply GlobalTheory.CxCoh.QAtFormal.qAt_formal <;> assumption)
