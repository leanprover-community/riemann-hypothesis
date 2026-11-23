module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv

theorem embedsBy_fA_of_isBCBasis (Rg : Type) [CommRing Rg] (B : Over (Sp Rg)) [GrpObj B] (M : LB B.left) (k mB : ℕ)
    (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (hB : IsAbelianScheme B) (hM : M.IsLB) (_hk : 1 ≤ k)
    (hVA : VeryAmpleAt B M k) (hb : IsBCBasis B M k bB) : GlobalTheory.AmpleSpan.EmbedsBy (GlobalTheory.HomFixUniv.fA B) bB := by
  have hp : IsProper B.hom := hB.proper
  let t : Spec (CommRingCat.of Rg) ⟶ (topS Rg).left := (Sp Rg).topIso.inv
  choose b' hb' using fun i => GlobalTheory.AbLaw.SecBC.exists_pullSec B M (k : ℤ) (homAt t) (bB i)
  have hspan := (hb Rg t b' hb').2
  have hE := GlobalTheory.AmpleSpan.embedsBy_baseAt B hM hVA (isAffineOpen_top (Sp Rg)) t b' hspan
  have hS := fun i => GlobalTheory.SpanFrame.secScal_of_isPullSec B hM (k : ℤ) (homAt t) (hb' i)
  haveI : IsIso (homAt t) := by
    haveI : IsIso ((Over.forget _).map (homAt t)) := by change IsIso t; infer_instance
    exact isIso_of_reflects_iso (homAt t) (Over.forget _)
  haveI : IsIso (homAt t ▷ B).left := inferInstanceAs (IsIso ((Over.forget _).map (homAt t ▷ B)))
  haveI : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of Rg)))
  have hw : (homAt t ▷ B).left ≫ fA B = (fst (baseAt t) B).left ≫ 𝟙 _ := by
    have e1 := Over.w (homAt t ▷ B)
    have e2 := Over.w (fst (baseAt t) B)
    have e3 : (baseAt t).hom = 𝟙 _ := by simp [baseAt, t, baseOver]
    rw [Category.comp_id, fA, e1, ← e2, e3, Category.comp_id]
  have sq : IsPullback (inv (homAt t ▷ B).left) (fA B) (fst (baseAt t) B).left (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [IsIso.inv_comp_eq, Category.comp_id, hw, Category.comp_id]
  exact GlobalTheory.AmpleSpan.EmbedsBy.secScal hM sq hE
    fun i => GlobalTheory.AmpleSpan.secScal_symm hM (hS i) (IsIso.inv_hom_id _)

end GlobalTheory.HomFixUniv
