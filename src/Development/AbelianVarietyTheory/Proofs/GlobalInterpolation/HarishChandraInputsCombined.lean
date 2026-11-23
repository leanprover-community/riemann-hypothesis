module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodIdempotentCoeffInvEqCoeff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotNeBotRead
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fc.KapLinked

section Rows

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}



theorem isot_ne_bot_of_rows (hF : GlobalTheory.Published.HarishChandraFinite) (hG : GlobalTheory.Published.GreenCuspidal) (t : RowsT K w Z Wt p0)
    (hM : GlobalTheory.CuspMult.MultEq t.r.z.R.toRealDat) (σ : Fin (w.D Z).what₂.Drows) (i : Fin (w.D Z).R.m) :
    (w.D Z).what₂.isot ((i : ℕ) + 1) ((w.D Z).what₂.ft σ) ≠ ⊥ := by
  have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hG
    (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) t.grp).2.1
  have hGS : Formalism.L2.DIV.GoodStable t.r.z.Xg := by
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL t.r.z.Xg t.r.z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [t.r.z.good.2, t.r.z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak t.r.z.R t.r.z.F t.r.z.pins.char t.exAt).1
  exact GlobalTheory.KapIsotRead.isot_ne_bot_read hF (w.st Z).toD7 _ _ _ _ _ _ t.r.z.R t.r.z.F t.r.z.cG p0 t.r.Y t.r.z.pins t.r.intersectionNumber_baseChange hM hGS
    (GlobalTheory.GoodTypeGeneric.chiIdem_mul_lvlIdem_base_ne_zero t.r.z.R.toRealDat t.r.z.F.lv2 t.r.intersectionNumber_baseChange.ok.ok2 hC.lev hC.grp _ hI) σ i



theorem goodTypes_of_rows (t : RowsT K w Z Wt p0) : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes t.r.z.R.toRealDat := by
  have hT : TypesTrue (w.st Z).toD7.ntypes t.r.z.R.C.P t.r.z.R.C.W := by
    rw [t.r.z.lev.C, w.C_eq]
    exact t.grp
  exact GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue t.r.z.pins.char.base.lev hT

end Rows


end GlobalTheory.Fc.KapLinked

end
