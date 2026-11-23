module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.IntTerm

theorem torsion_lies_under : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V →
    ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G]
      [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (N : ℕ), 1 ≤ N →
      ∀ β : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ D.toPre.P.A, β ^ N = 1 →
      ∃ xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ A.A, xb ^ N = 1 ∧
        (∃ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 ∧
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb) ∧
        ∀ p : QkPt D.toPre (AlgebraicClosure (FractionRing V)) N, p.y = 0 →
          QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) N p xb → p.g.b = β := by
  intro V _ _ _ hCN D A G _ _ hG U N hN β hβ
  haveI : CharZero V := hCN.2.2.2
  have hA := GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨f, hf⟩ := GlobalTheory.TorsionIso.torsion_eq GlobalTheory.firstFiveLaws V (maximalIdeal V) hA D A G hG U
    (AlgebraicClosure (FractionRing V)) N hN
  obtain ⟨p, hpy, hpb⟩ := GlobalTheory.TorusExt.exists_qkPt_of_torsion (F := AlgebraicClosure (FractionRing V))
    D.tau_bimult (n := N) (by omega) hβ
  refine ⟨f p, ?_, ⟨p, hpy, (hf.1 p (f p)).2 rfl⟩, fun p' hp'y hp' => ?_⟩
  · obtain ⟨w, hw⟩ := U.ext
    exact ((hf.1 p (f p)).2 rfl w hw).1
  · have e : f p = f p' := (hf.1 p' (f p)).1 hp'
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    obtain ⟨z, hy, w, hw₁, hw₂⟩ := (hf.2.2.1 p p').1 e
    have hg := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hw₂
    rw [hp'y, hpy, zero_add] at hy
    have hz : z = 0 := by
      have h2 : (N : ℤ) • z = 0 := by rw [natCast_zsmul]; exact hy.symm
      rcases smul_eq_zero.1 h2 with h | h
      · omega
      · exact h
    subst hz
    have hw : w.b = 1 := by
      exact hw₁.1.trans (cPoint_zero _)
    rw [hg, GlobalTheory.TorusExt.add_b, hw, _root_.mul_one, hpb]

end GlobalTheory.Poinc.IntTerm
