module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 Formalism.IndefR Formalism.IndefR.Links
namespace GlobalTheory.Fam

theorem xi_chrEq_cols_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ t, Formalism.IndefR.Links.ChrEq ((_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xi t) (q.w.I.xi (b.P.I.tup t)) := by
  intro hL p K q c b hw
  obtain ⟨x, a, ax, y, recPin, s, pt, sx, eF, cW, d3b, side, colPins⟩ := hw
  have key : ∀ t : x.T, Formalism.IndefR.Links.ChrEq (x.R.toRealDat.xi t) (q.w.I.xi (x.Y.tup t)) := by
    have hxi : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → HEq (x.R.toLevCh.xiH (x.Y.tupT μ)) (q.w.I.xi μ) := by
      have h := eq_of_heq ax
      rw [← h]
      exact fun μ hμ => ((GlobalTheory.Mem.R3.twArgs_lev K q.B q.f q.T q.w q.Z _ _ _ _ _ _ _ _ _ _ a).2.2.1 μ hμ).2
    intro t
    have hu : Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) (x.Y.tup t) := by
      rcases x.pins.char.tup.mu_used t with h | ⟨w, h⟩
      · rw [h]; exact Or.inl x.Y.tup0
      · rw [← h]
        obtain ⟨w', rfl⟩ := (q.w.D q.Z).plEq.surjective w
        exact Or.inr ⟨w', (x.Y.muAt w').symm⟩
    have h1 := hxi _ hu
    rw [x.Y.tupT_tup] at h1
    have h2 := x.pins.char.base.lev.xi t
    rw [eq_of_heq h1] at h2
    exact h2
  show (fun k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S => ∀ t : k.P.T, Formalism.IndefR.Links.ChrEq (k.B.Q.Rl.toRealDat.xi t) (q.w.I.xi (k.P.I.tup t))) (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b)
  rw [y.eq]
  exact key
end GlobalTheory.Fam
end
