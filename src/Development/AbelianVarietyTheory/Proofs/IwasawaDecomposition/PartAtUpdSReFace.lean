module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScalarsZeroPartConventionFixedPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem lamN_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (kap : ℝ)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v) {p} (hp : R.EEp3 p ≠ ⊥) (t j) :
    (R.updS kap (zeroLam R F c)).lamN t j p = R.lamN t j p := by
  unfold RealDat3.lamN
  split_ifs with h
  · exact scalarsZeroPartConvention_fixedPlace R F c ((hZ p hp _).1)
  · rfl

theorem isKap_congr {N Tup Sig : Type} [AddCommGroup N] [Module ℂ N] {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam lam' : Tup → ℕ → Sig → ℝ} {κ : ℝ} (h : Lift.IsKap m dnup partE lam κ)
    (hl : ∀ μ j σ, partE σ ≠ ⊥ → lam' μ j σ = lam μ j σ) : Lift.IsKap m dnup partE lam' κ := by
  intro μ σ x hx
  by_cases hσ : partE σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp only [map_zero, smul_zero]
  · rw [Finset.prod_congr rfl fun j _ => hl μ j σ hσ]
    exact h μ σ x hx

theorem isLamP_congr {A Amb Sig : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb] {thW : A →ₗ[ℂ] Amb}
    {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb} {lam lam' : Sig → ℝ} (h : Lift.IsLamP thW adj part lam)
    (hl : ∀ σ, part σ ≠ ⊥ → lam' σ = lam σ) : Lift.IsLamP thW adj part lam' := by
  intro σ x hx
  by_cases hσ : part σ = ⊥
  · rw [hσ, Submodule.mem_bot] at hx
    subst hx
    simp only [map_zero, smul_zero]
  · rw [hl σ hσ]
    exact h σ x hx



theorem thmB_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ) (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hB : R.PThmB) : (R.updS R.kap (zeroLam R F c)).PThmB := by
  let S := R.updS R.kap (zeroLam R F c)
  change Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 S.lamN R.kap
  exact isKap_congr (lam := R.lamN) hB fun μ j _ hσ => lamN_zeroLam R F c R.kap hZ hσ μ j



theorem thmA_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hA : R.PThmA) : (R.updS R.kap (zeroLam R F c)).PThmA := by
  intro i t
  change Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (R.Wp3 i)
    (fun p => zeroLam R F c i t p A3.A.v0)
  exact isLamP_congr (lam := fun p => R.lam3 i t p A3.A.v0) (hA i t)
    fun p hp => scalarsZeroPartConvention_fixedPlace R F c (i := i) (t := t) (p := p) hp



private theorem toCx3_updS_eq_reScal (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam) :
    (R.updS kap lam).toCx3 F = reScal (R.toCx3 F) (fun _ => kap) lam := by
  rfl

theorem galD_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3) (c : Fin D.R.m → ℝ)
    (hG : (R.toCx3 F).GalD F.cr false) : ((R.updS R.kap (zeroLam R F c)).toCx3 F).GalD F.cr false := by
  rw [toCx3_updS_eq_reScal]
  exact cx_galD_scal (R.toCx3 F) F.cr (fun _ => R.kap) (zeroLam R F c)
    (fun j p v hv hp => zeroLam_off R F c (i := j) (t := A3.A.μ0) (p := p) (v := v) hv hp) hG

theorem partAt_updS_reFace (R : RealDat3 D A3 Ks) (F : Face3 D A3) (kap lam)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (i p v) :
    (R.updS kap lam).PartAt (reFace F Dc Sp Zsc) i p v ↔ R.PartAt F i p v :=
  (RealDat3.partAt_updS kap lam i p v).trans Iff.rfl

private theorem toCx3_reFace_eq (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) :
    R.toCx3 (reFace F Dc Sp Zsc) = R.toCx3 F := by
  rfl

private theorem simX_reFace_iff (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (X : CxData A3.fam3.amb3) (i p v l) :
    SimX (reFace F Dc Sp Zsc).cr X false i p v l ↔ SimX F.cr X false i p v l := by
  dsimp only [SimX, CxData.liftMat, CxData.liftMatC, CxData.tC,
    Face3.cr, Face3.fc, reFace, faceOf3, crdOf3, lv]
  rfl

theorem scal_zeroLam (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (hZ : ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v)
    (hs : R.IsScal F) :
    (R.updS R.kap (zeroLam R F (Zsc (R.toCx3 F).zs).l6m)).IsScal (reFace F Dc Sp Zsc) := by
  let c := (Zsc (R.toCx3 F).zs).l6m
  let lam := zeroLam R F c
  let S := R.updS R.kap lam
  let F' := reFace F Dc Sp Zsc
  change S.IsScal F'
  have hpart (i p v) : S.PartAt F' i p v ↔ R.PartAt F i p v :=
    partAt_updS_reFace R F R.kap lam Dc Sp Zsc i p v
  have hlam (t j p) (hp : R.EEp3 p ≠ ⊥) : S.lamN t j p = R.lamN t j p :=
    lamN_zeroLam R F c R.kap hZ hp t j
  have hface : S.toCx3 F' = S.toCx3 F := toCx3_reFace_eq S F Dc Sp Zsc
  have hzs : (S.toCx3 F').zs = (R.toCx3 F).zs :=
    (congrArg CxData.zs hface).trans (RealDat3.zs_updS (R := R) (F := F) R.kap lam)
  have hscale : (F'.Zsc (S.toCx3 F').zs).l6m = c := congrArg (fun zs => (Zsc zs).l6m) hzs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t p l hp hl
    change lam i t p A3.A.v0 = l
    exact (scalarsZeroPartConvention_fixedPlace R F c (i := i) (t := t) (p := p) hp).trans
      (hs.lam0 i t p l hp hl)
  · intro κ hk hne
    have hk' : Lift.IsKap D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) R.EEp3 S.lamN κ := hk
    refine hs.kap κ (isKap_congr (lam' := R.lamN) hk' fun t j p hp => (hlam t j p hp).symm) ?_
    obtain ⟨t, p, hp, hne⟩ := hne
    change R.EEp3 p ≠ ⊥ at hp
    have hprod : (∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p) =
        ∏ j ∈ Finset.Icc 1 D.R.m, R.lamN t j p :=
      Finset.prod_congr rfl fun j _ => hlam t j p hp
    exact ⟨t, p, hp, hprod ▸ hne⟩
  · intro i p v l hv hp he
    change lam i A3.A.μ0 p v = l
    have hp' := (hpart i p v).mp hp
    have hsim : SimX F'.cr (S.toCx3 F') false i p v l := he
    rw [hface] at hsim
    have hsim' : SimX F.cr (R.toCx3 F) false i p v l :=
      (RealDat3.sim_updS (R := R) (F := F) R.kap lam i p v l).mp
        ((simX_reFace_iff F Dc Sp Zsc (S.toCx3 F) i p v l).mp hsim)
    exact (zeroLam_off R F c (i := i) (t := A3.A.μ0) (p := p) (v := v) hv hp').trans
      (hs.off i p v l hv hp' hsim')
  · intro i t p hp
    change lam i t p A3.A.v0 = Real.exp ((F'.Zsc (S.toCx3 F').zs).l6m i)
    rw [hscale]
    exact zeroLam_of_zero R F c (i := i) (t := t) (p := p) (v := A3.A.v0) (Or.inl ⟨rfl, hp⟩)
  · intro i p v hv hp
    change lam i A3.A.μ0 p v = Real.exp ((F'.Zsc (S.toCx3 F').zs).l6m i)
    rw [hscale]
    exact zeroLam_of_zero R F c (i := i) (t := A3.A.μ0) (p := p) (v := v)
      (Or.inr ⟨hv, fun h => hp ((hpart i p v).mpr h)⟩)
  · intro i t p v hv
    change zeroLam R F c i t p v = zeroLam R F c i A3.A.μ0 p v
    unfold zeroLam
    split_ifs
    · rfl
    · exact hs.tup i t p v hv

end GlobalTheory.Mem.R3

end
