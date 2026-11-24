module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedSectionsTateTwistResolution
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem _root_.GlobalTheory.T.supportedSections_tateTwist_resolution : ∀ (q : ℕ) [NeZero q] (i : ℤ) (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U, Function.Injective (Sec.map (ι.f n) (U := U))) → (∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) → ∃ e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (D.X 0) U, IsTwRes q i D e ∧ ∀ U ζ, Sec.map (ι.f 0) (e U ζ) = resGen i ζ := by
  first
  | exact @GlobalTheory.EtC.SuppRes.supp_res
  | exact GlobalTheory.EtC.SuppRes.supp_res
  | (intros; apply GlobalTheory.EtC.SuppRes.supp_res <;> assumption)
