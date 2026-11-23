module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartSel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PlugPt
open GlobalTheory.Mem.R3 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

theorem sidePt_part_of_pack_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (t : b.Comparison₂) {x : R3.TwIn O.ex}
    (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (h : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) :
    ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp t.1.Tp ∧
      sidePt (O := O) (b.part t).pt = ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
  have key : ∀ (p : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S) (_ : p = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) (Tq : Formalism.L2.Host.TupTied D p.B.Q.Rl.C O.ex.nch),
      ∃ Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch, HEq Tp Tq ∧
        ({ G := p.P.Gp, Pl0 := p.P.Pl0, I0 := p.P.I0, T := p.P.T, A3 := p.P.A3, J := p.B.T, alg := p.B.alg, R := p.B.Q.Rl, P0 := p.P.P0, ψ0 := p.P.ψ0, cG := p.B.Q.cG, v₀ := p.B.v₀, S := p.B.Q.Sx, YS := p.B.Q.nexp, cf := p.B.Q.Rl.C, tp := Tq } : Side D O.ex.nch) =
          ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := y.Sx, YS := y.nexp, cf := x.R.C, tp := Tp } : Side D O.ex.nch) := by
    intro p hp Tq
    subst hp
    exact ⟨Tq, HEq.rfl, rfl⟩
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) h t.1.Tp

theorem pin_pt_of_bundle_witness : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (hE : _root_.GlobalTheory.PlugPt.HasExponent' N) (K : Ctx) (q : WPt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (_ : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness (p := _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) q b) (t : b.Comparison₂), _root_.GlobalTheory.PlugPt.pinnedPointOfReading (_root_.GlobalTheory.PlugPt.ExtensionReading.of RX hE (SXE S) (OX Γ)) K q c (b.part t).pt := by
  intro hL N S Γ hE K q c b w t
  obtain ⟨x, a, ax, y, recPin, -, -, sx, eF, fi, -⟩ := w
  obtain rfl := eq_of_heq ax
  obtain ⟨Tp, hTp, h⟩ := _root_.GlobalTheory.PlugPt.sidePt_part_of_pack_alt b t y.y y.eq
  have htp : HEq Tp q.x.n.tp := hTp.trans (t.1.tpEq.trans (Sigma.mk.inj_iff.mp recPin.s.chr).2)
  have hcf : q.x.what₂.r.z.R.C = GlobalTheory.Mem.Col2.TC.cf q.w.I q.w.l q.Z := q.x.what₂.r.z.lev.C
  refine ⟨q.x.what₂.r.z.R.kap, a.lam, a.err, h.trans ?_⟩
  refine side_eq_upd (O := q.O) a.x (_root_.GlobalTheory.PlugPt.sideOf_alt q.x.what₂ q.x.n q.core_data_of_point) q.x.what₂.r.z.R.kap a.lam a.err (reFace q.x.what₂.r.z.F a.Dc a.Sp a.Zsc :)
    y.y.Sx y.y.nexp Tp ?pack rfl HEq.rfl ?v ?S ?fi ?eF hcf htp
  case pack => exact (by with_unfolding_all exact (a.pack :))
  case v => exact (by with_unfolding_all exact (a.v₀ :))
  case S => exact (by with_unfolding_all exact (sx :))
  case fi => exact (by with_unfolding_all exact (fi :))
  case eF => exact (by with_unfolding_all exact (eF :))
end GlobalTheory.PlugPt
end
