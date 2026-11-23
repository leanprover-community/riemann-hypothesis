module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheoremStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_obj_and_abc : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  intro k G _ _ l n _ _ _ R F r Dt M A N h
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := h
  have oB : F.Obj B := M.base_obj B Nb hB
  have o1 : F.Obj A₁ := F.obj_sub A₁ B j hj hji oB
  have oA : F.Obj A := F.obj_quot A₁ A p hp hps o1
  obtain ⟨h1, h2, h3⟩ := M.base_abc B Nb hB
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.phiGammaModule_saturation_theorem R (F.D B) (F.D A₁) (F.map A₁ B j)
    (F.map_inj A₁ B j o1 oB hj hji) (F.map_φ A₁ B j o1 oB hj) (F.map_γ A₁ B j o1 oB hj)
    Dt.w Dt.wst Nb h1 h2 h3
  exact ⟨oA, GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective R (F.D A₁) (F.D A) (F.map A₁ A p)
    (F.map_surj A₁ A p o1 oA hp hps) (F.map_φ A₁ A p o1 oA hp) (F.map_γ A₁ A p o1 oA hp)
    Dt.w Dt.wst (F.pre A₁ B j Nb) s1 s2 s3⟩

end GlobalTheory.Models
