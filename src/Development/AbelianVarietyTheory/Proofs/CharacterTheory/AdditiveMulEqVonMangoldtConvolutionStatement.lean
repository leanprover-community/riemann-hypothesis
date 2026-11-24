module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveMulEqVonMangoldtConvolution
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

open Polynomial GlobalTheory.CuspGL

theorem _root_.GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution : ∀ (F : Type) [Field F] (q : ℕ), 2 ≤ q → ∀ (s m : F[X] → ℂ), IsAdditive s → m 1 = 1 → (∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P) → ∀ P : F[X], P.Monic → s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  first | exact @GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv | exact GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv | (intros; apply GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv <;> assumption)
