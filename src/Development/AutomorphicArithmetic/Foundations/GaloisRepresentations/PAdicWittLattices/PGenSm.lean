module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfCompactB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pGenSm : GenSm := by
  intro p _ D R _ _ gb N X
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2
  obtain ⟨j, hoi, hci, hj, -⟩ := GenCmp.genModel_eq_genericFibre p D R (GenCmp.baseOf gb) R (RingHom.id R) gb
    rfl (fun _ => rfl) N.1 N.2.1 N.2.2 M X
  haveI := hoi
  haveI := hci
  haveI : IsQProjOver M.s := M.qproj
  haveI : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
  haveI : IsSeparated M.s := GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj
  haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  rw [← hj]
  refine ⟨inferInstance, inferInstance, inferInstance, fun hB => ?_⟩
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (RingHom.id R)
      (Model.isProjOver_of_compactB p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2 hB M))
