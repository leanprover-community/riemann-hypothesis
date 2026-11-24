module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.QuoDMk

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb.LsG

open CrystallineSemistableComparison.Ls

variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  (F : B.Fn O) (ρ : O →+* k)

def thW (m : ℕ) : PDF (WittVector l k) (Thick (Wc.L l F ρ m)) where
  A := Wc.OA l F ρ m
  J := ⟨fun T => T.J, fun φ _ hx => φ.hle hx⟩
  dp {T} n x := T.δ.dpow n x
  dp_zero {T} _ hx := T.δ.dpow_zero hx
  dp_one {T} _ hx := T.δ.dpow_one hx
  dp_zero_right {T} _ hk := T.δ.dpow_eval_zero hk
  dp_add {T} n _ _ hx hy := T.δ.dpow_add hx hy
  dp_map φ n x hx := (φ.dp.2 x hx).symm

abbrev fl (m : ℕ) : ObjectProperty (Thick (Wc.L l F ρ m)) := FlatT

abbrev sW (m : ℕ) : PDF (WittVector l k) (fl l F ρ m).FullSubcategory := (thW l F ρ m).res (fl l F ρ m).ι

abbrev Kt (m : ℕ) : Cx.{1} (WittVector l k) := CH.cx (CH.modF (sW l F ρ m).A)

theorem modF_sW (m : ℕ) : CH.modF (sW l F ρ m).A = (fl l F ρ m).ι ⋙ Wc.OM l F ρ m := rfl

def resF (m j : ℕ) : (Wc.HS l F ρ j).M m →ₗ[WittVector l k] (Kt l F ρ m).H j :=
  (CH.Mor.restrict (Wc.OM l F ρ m) (fl l F ρ m).ι).pull j

end CrystallineSemistableComparison.Pb.LsG

end
