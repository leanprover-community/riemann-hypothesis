module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_id_apply (hHl : TrHl) (hL : TrLin) (hW : WtLin) (l : ℕ) [Fact l.Prime] (n i : ℤ) (S : Scheme.{0})
    (d : ℤ) (hu : IsUnit (l : Γ(S, ⊤))) (x : Hl l (sch.obj S) n i) :
    trHl l (𝟙 S) (Wt.const S d) n i x = d • x := by
  have hw : IsWt (𝟙 S) (Wt.const S d) := hW.2.2 (𝟙 S) d
  refine Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hu.pow k
  refine (hHl l n i (𝟙 S) _ hw hu x k).trans ?_
  exact (hL (l ^ k) n i).2.2 S d hq (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trIdQ_of :
    TrHl → TrLin → WtLin → TrIdQ := by
  intro hHl hL hW l _ n i S d hu
  unfold trHQ
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [LinearMap.baseChange_tmul, trHl_id_apply hHl hL hW l n i S d hu m]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, TensorProduct.tmul_smul]
    rw [Int.cast_smul_eq_zsmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
