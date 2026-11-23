module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjSpace
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

@[expose] public section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.ArchInt

theorem continuousOn_logNorm_offSupp {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {q : X ⟶ Sp k} {σ : k →+* ℂ} {L : LB X} (ψ : GlobalTheory.Weight q σ L) (hψ : ψ.IsCInf)
    {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) :
    ContinuousOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) := by
  intro y hy
  obtain ⟨i, hi⟩ := GlobalTheory.CxPts.exists_mem_ptsIn (p := q) (σ := σ) ψ.isLB.cover y
  have hu : GlobalTheory.Cartier.UnitAt (GlobalTheory.Cartier.under y) ((r i : X.functionField)) :=
    GlobalTheory.Cartier.IsRatSec.unitAt ψ.isLB hr hy hi
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.Cartier.UnitAt.exists_nhds hu
  have hgV : genericPoint X ∈ V := GlobalTheory.Cartier.gen_mem hyV
  obtain ⟨a, ha⟩ := GlobalTheory.Cartier.exists_unit_fnOf_eq hV
  have hyV' : y ∈ GlobalTheory.CxPts.ptsIn q σ V := GlobalTheory.CxPts.mem_ptsIn.2 hyV
  have hNo : IsOpen (GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr)) :=
    ((GlobalTheory.CxPts.isOpen_ptsIn V).inter (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
      (GlobalTheory.Cartier.isOpen_offSupp _)
  have hyN : y ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr) := ⟨⟨hyV', hi⟩, hy⟩
  have heq : ∀ z ∈ GlobalTheory.CxPts.ptsIn q σ V ∩ GlobalTheory.CxPts.ptsIn q σ (L.U i) ∩
      GlobalTheory.Cartier.offSupp q σ (divOfRatSec ψ.isLB hr),
      Real.log ‖GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2 =
        GlobalTheory.Cartier.logNorm ψ r z := by
    rintro z ⟨⟨hzV, hzi⟩, hz⟩
    rw [GlobalTheory.Cartier.logNorm_eq ψ hr hz hzi, ← ha hgV, GlobalTheory.Cartier.ratVal_fnOf hzV]
  have hne : GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V)) y ≠ 0 := by
    rw [← GlobalTheory.Cartier.ratVal_fnOf hyV' hgV, ha hgV]
    exact GlobalTheory.Cartier.ratVal_ne_zero hu
  have hev : ContinuousAt (GlobalTheory.CxPts.ev q σ V (a : X.presheaf.obj (Opposite.op V))) y :=
    (GlobalTheory.CxPts.continuousOn_ev _).continuousAt ((GlobalTheory.CxPts.isOpen_ptsIn V).mem_nhds hyV')
  have hφ : ContinuousAt (ψ.φ i) y := (hψ i y hi).continuousAt
  have hg : ContinuousAt (fun z => Real.log ‖GlobalTheory.CxPts.ev q σ V
      (a : X.presheaf.obj (Opposite.op V)) z‖ - ψ.φ i z / 2) y :=
    (hev.norm.log (norm_ne_zero_iff.2 hne)).sub (hφ.div_const 2)
  exact (hg.congr (Filter.eventuallyEq_of_mem (hNo.mem_nhds hyN) heq)).continuousWithinAt

end GlobalTheory.CompanionTheory.MixZ.ArchInt
