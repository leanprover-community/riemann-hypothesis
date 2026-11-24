module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.TowerRallisLemma
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
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

namespace CrystallineSemistableComparison.Onto

structure Parts : Prop where
  mv : MVBij
  surj : OneSurj
  cov : CovDesc
  site : SiteLaws
  on : OnIso
  zar : ZarAbs
  aff : AffOm
  nat : OmNat
  laws : FormLaws
  dw : DWedge
  dl : DLog
  kun : OmKun
  fc : FormCup
  c1 : FirstChernCoboundary
  div : DivCover
  chart : ChartLaws
  bij : ChartBij
  iso : IsoBij
  cup : CupLaws
  zarRel : ZarRelOf
  affRel : AffRelOf
  lift : RelLiftOf
  inj : RelInjOf
  cone : ConeKillOf
  kill : RelKillOf
  kunAff : KunAffOf
  slant : SlantOf
  killOf : KillOf3
  onto : OntoOf3
  low : OntoLow
  retr : Retract

theorem Parts.hodgeKill (h : Parts) : HodgeKill :=
  have zr := h.zarRel h.site h.on h.zar
  h.killOf h.site h.cup (h.lift h.site h.on) (h.inj h.site h.mv h.cov zr h.chart h.bij h.iso)
    (h.kill h.site h.cov zr h.aff h.nat (h.affRel h.site h.on h.aff h.nat h.laws) h.laws h.dw h.dl h.fc h.c1 h.div (h.cone h.surj))

theorem Parts.slant' (h : Parts) : Slant :=
  h.slant h.site h.mv h.cov h.zar h.aff (h.kunAff h.site h.aff h.nat h.laws h.fc h.kun)

theorem ontoAll_of (h : Parts) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : OntoAll :=
  h.low h.cup h.retr (h.onto h.cup h.slant' h.hodgeKill hS hD hF)

end CrystallineSemistableComparison.Onto
