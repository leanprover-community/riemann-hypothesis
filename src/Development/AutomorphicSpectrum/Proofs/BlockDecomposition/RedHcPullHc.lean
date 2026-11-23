module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SchFnPtTw
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.CrisTransition

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

def redFn (F : Fn O) (κ : O →+* OC l) (k : Bool) {m n : ℕ} (h : n ≤ m) :
    Mor (Lc F κ k m) (Lc F κ k n) ((base l).red h) :=
  B.crMor (F := F) (F' := F) (b := bs l k m) (b' := bs l k n) (ht := rfl) (ht' := rfl) ((base l).red h) rfl
    (dd_red k _ h) (basePt F _ (red_κb κ k h)) fun _ _ _ => rfl

theorem redHc_pullHc {F F' : Fn O} (κ : O →+* OC l) (u : Fn.Map F F') (k : Bool) {m n : ℕ} (h : n ≤ m) (j : ℕ)
    (x : Hc F' κ k m j) : redHc F κ k h j (pullHc κ u k m j x) = pullHc κ u k n j (redHc F' κ k h j x) := by
  unfold redHc pullHc redMor pullMorC
  exact cr_square (SH.pullM κ u k m) (redFn F κ k h) (redFn F' κ k h) (SH.pullM κ u k n) (SH.idc _)
    (red_cris _ h) (red_cris _ h) (SH.idc _) (fun r => (SH.idc ((base l).red h) r).symm)
    (SH.base_map u (red_κb κ k h)) j x

end GlobalTheory.CompanionTheory.CrisTransition
