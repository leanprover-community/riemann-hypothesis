module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ToBSurj
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {m : ℕ}

section
variable (L : Lev R m) (M : Model l K) (s : ℕ)

abbrev QA : ObjectProperty (Thick (nlFun L.γ 0 M.X M.p (κA (OK l K) L.I))) := TS L.γ M.p l s {⊤}

abbrev QB : ObjectProperty (Thick (nlFun L.γB 0 M.gen M.q (κA K L.IB))) := TS L.γB M.q 1 s {⊤}


variable {L} in
def nmB (hL : L.Good) : NMor L.γ M.p (κA (OK l K) L.I) L.γB M.q (κA K L.IB) L.ι where
  hI := hL.ι_dp
  u := pullback.fst _ _
  g := (OK l K).subtype
  hu := pullback.condition
  hκ a r h := by
    have h1 : algebraMap (OK l K) L.A a - r ∈ L.I := Ideal.Quotient.eq.1 h
    rw [hL.ι_I, Ideal.mem_comap, map_sub, hL.ι_O] at h1
    exact Ideal.Quotient.eq.2 h1


variable {L} in
def smB (hL : L.Good) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) :
    SMor (sP (QA L M s)) (sP (QB L M s)) L.ι :=
  (nmB M hL).smor (QA L M s) (QB L M s) hQ


variable {L} in
def bMap (hL : L.Good) (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T)) (j : ℕ) :
    HO (QA L M s) j →ₛₗ[L.ι] HO (QB L M s) j :=
  (smB M s hL hQ).o.pull j

end

def Lev.CrisOK {m : ℕ} (L : Lev (per l K) m) : Prop :=
  L.lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ L.I ∧
  ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
    algebraMap (OK l K) L.A a - L.lam (algebraMap (Ainf l) (Acris l) w) ∈ L.I

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))

def chainOf (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) :
    Chain.{1} (per l K).A L.A L.B K where
  ℓ := l
  S n j := M.Hc false n j
  Zn n j := HM (QA L M s) none ((l : L.A) ^ n) j
  Z j := HO (QA L M s) j
  W j := HO (QB L M s) j
  V j := HdR M.q j
  lam := L.lam
  ι := L.ι
  o := algebraMap K L.B
  tS n j := (M.HS false j).r n
  tZ n j := trM (QA L M s) none (l : L.A) n j
  r := rH
  red n j := redM (QA L M s) none ((l : L.A) ^ n) j
  b j := bMap M s hL hQ j
  μ j := muB L.γB M.q 1 s {⊤} j

end

end CrystallineSemistableComparison.Pb.Kap
