module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiMapEqOfFlatTateTwistResolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.semiMap_eq_of_flat_tateTwist_resolution : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (k : ℤ) {T : Cx (ZMod Q)} (e : ∀ U : Scheme.{0}, Prim Q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes Q k T e → (∀ t, FlatS (T.X t)) → ∀ σ σ' : SemiMap T (res _ (tw q k)), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), σ.app U 0 (e U ζ) = σ'.app U 0 (e U ζ)) → ∀ (E : Spc) (n : ℤ) (x : CohomologyClass ((chains (ZMod Q)).obj E) T n), σ.op.app E n x = σ'.op.app E n x := by
  first | (exact @GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (exact GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res) | (intros; apply GlobalTheory.EtC.ScalarExt.semiMap_op_eq_of_flat_res  <;> assumption)
