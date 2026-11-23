module

public import Mathlib.RingTheory.Length
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Pointwise

theorem _root_.GlobalTheory.T.length_quotient_smul_sup_le_intermediate : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (Z B B' : Submodule O A) (a : O), B ≤ B' → Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤ Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id : (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) + Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  first | exact @GlobalTheory.length_quotient_smul_sup_le | exact GlobalTheory.length_quotient_smul_sup_le | (intros; apply GlobalTheory.length_quotient_smul_sup_le <;> assumption)
