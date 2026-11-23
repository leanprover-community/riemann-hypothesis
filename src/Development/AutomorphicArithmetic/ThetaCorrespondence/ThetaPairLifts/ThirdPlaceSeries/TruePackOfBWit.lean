module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TruePack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColsStdOfBWit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkHypOfReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealAtColsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAtOfBWitStatement
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem truePack_of_bWit_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → Nonempty (Bl.RXs q.x.what₂) → _root_.GlobalTheory.Fam.BundlePointConditions b → _root_.GlobalTheory.Fam.TruePackAlt (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hW hX hR
  obtain ⟨hOk, hPins, hTw, hStdC, hTS⟩ := _root_.GlobalTheory.Fam.colsStd_of_bWit_alt q b hW
  obtain ⟨hChr, hXi, hQ, hLev, hRec, hRP, hOk3, hIdE, hLM⟩ := _root_.GlobalTheory.T.characters_match_bundle_alt q b hW
  have hTop := _root_.GlobalTheory.T.exists_read_at_packB_of_bWit q b hW hX
  have hTW : _root_.GlobalTheory.Fam.ValidRealPackage (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hOk, hPins, hTw, hStdC, hChr, ⟨1, hTop⟩⟩
  have hTQ : _root_.GlobalTheory.Fam.GeometricFamilyConditions (_root_.GlobalTheory.Fam.packB_alt b) := ⟨hXi, hQ, hTop⟩
  obtain ⟨hRec'⟩ := hRec
  have hPk : _root_.GlobalTheory.Fam.PackageHypotheses (_root_.GlobalTheory.Fam.packB_alt b) := _root_.GlobalTheory.Fam.pkHyp_of_real_alt (_root_.GlobalTheory.Fam.packB_alt b) hR.join hLM hR.dc hR.frames hRP hR.see hRec' hR.ex hR.prim.1 hR.prim.2
    hOk3 hIdE hR.gapS hR.fin hR.gap hTW hTQ
  exact _root_.GlobalTheory.Fam.TruePackAlt.mk _ ⟨hPk, hTW, hTQ, hTS, hLev, ⟨hRec'⟩⟩
end GlobalTheory.Fam
end
