module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimitBilinearCup.CupAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
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

open CategoryTheory GlobalTheory.LogCris

namespace CrystallineSemistableComparison.CupAbs

variable {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} (m : GlobalTheory.LogCris.Mor L L' σ) {Λ Λ' : Type}
  [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R} (σ₀ : Λ →+* Λ') (h : ∀ a, σ (c a) = c' (σ₀ a))

theorem om_cup {p q n : ℕ} (e : p + q = n) (x : CH.H (B.OM L c) p) (y : CH.H (B.OM L c) q) :
    (B.omMor m σ₀ h).pull n ((CH.mulP (B.OA L c)).cup e x y) =
      (CH.mulP (B.OA L' c')).cup e ((B.omMor m σ₀ h).pull p x) ((B.omMor m σ₀ h).pull q y) :=
  P.cup_pull (CH.mulP (B.OA L c)) (CH.mulP (B.OA L' c')) (B.omMor m σ₀ h).G (B.omMor m σ₀ h).τ (B.omMor m σ₀ h).τ
    (B.omMor m σ₀ h).τ (B.omMor m σ₀ h).nat (B.omMor m σ₀ h).nat (B.omMor m σ₀ h).nat (fun _ _ _ => rfl) e x y

theorem om_one : (B.omMor m σ₀ h).pull 0 (CH.oneH (B.OA L c)) = CH.oneH (B.OA L' c') :=
  pull_one (B.omMor m σ₀ h) (fun _ => rfl)

end CrystallineSemistableComparison.CupAbs
