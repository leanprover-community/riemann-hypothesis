module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.KProps
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

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers GroundTheory.PAdicHodge Formalism.Per6

namespace CrystallineSemistableComparison.HT

open PAlg Pb

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))


variable (l) in
def CrisSurj : Prop := ∀ n, Function.Surjective ((base l).cris n)

def cb (ht : TFil l) (hs : CrisSurj l) : CB l K where
  Λ := Acris l
  R n := (base l).Acr n
  I n := B.JJ false (base l) n
  γ n := B.DD false (base l) n
  κ n := B.κb (okToOC l K) false n
  c n := (base l).cris n
  c_surj := hs
  t := tA l
  ht := ht (base l)
  θ := θA l
  rd n := (base l).red n.le_succ
  rd_dp n := B.dd_red false _ n.le_succ
  rd_κ n := B.red_κb _ false n.le_succ
  rd_c n := B.red_cris _ n.le_succ

variable {K} (ht : TFil l) (hs : CrisSurj l) {M : Model l K}

def toY {r j : ℕ} (x : Fam M r j) : (cb K ht hs).Fam M r j := x

theorem toY_comp {r j : ℕ} (x : Fam M r j) : CB.Comp (toY ht hs x) ↔ Comp x := Iff.rfl

theorem toY_isFirstChern_iff (D : E.LineData M.X) (x : Fam M 1 2) : CB.IsFirstChernClassInFamily D (toY ht hs x) ↔ IsFirstChernClassInFamily D x := Iff.rfl

variable (l K)

def LvEx : Prop := ∀ (ht : TFil l) (hs : CrisSurj l), Nonempty (LvSys (cb K ht hs) (Γ := K.fixingSubgroup)
  (fun σ => ACris.galCris (IntermediateField.fixingSubgroupEquiv K σ)) (fun σ => galBase (IntermediateField.fixingSubgroupEquiv K σ))
  (fun σ => (period_ring_base.σC σ.1).toRingHom) fun σ => qC l (period_ring_base.χ σ.1))

def Half2Of : Prop := ∀ ht : TFil l, CrisSurj l → LvEx l K → RhoEx l K → CoEx l K → HomRho l K → HomMu l K → MulRho l K →
  FirstChernHodgeTateCompat l K → KForm → KFin → ∃ γ, Half2 (K := K) ht γ

end CrystallineSemistableComparison.HT
