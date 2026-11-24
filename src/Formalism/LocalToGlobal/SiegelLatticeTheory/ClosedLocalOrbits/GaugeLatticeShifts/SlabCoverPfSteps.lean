module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.KExpCut
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def GFInfInj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (s : X.B.I.GA), s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → s.1 = 1 → s = 1

def NStrongApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (n : X.B.I.Gf),
    X.LevelSubgroupNormalized → n ∈ X.NfinU u → ∃ ν ∈ Srat X u,
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * (ν.2 * n) * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NDense : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (n : X.B.I.Gf), n ∈ X.NfinU u →
    ∀ U : Set X.B.I.Gf, IsOpen U → n ∈ U →
      ∃ ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, ν.1 ∈ X.NinfU u ∧ ν.2 ∈ X.NfinU u ∧ ν.2 ∈ U

def NLift : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (t : X.B.I.Ginf),
    t ∈ NOcol (X.Fu u) (Y.cs u) ρ → ∃ s ∈ Srat X u, s.1 = t ∧
      (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * s.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2

def NRatLam : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (ν : X.B.I.GA),
    X.LevelSubgroupNormalized → ν ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I → ν.1 ∈ X.NinfU u → ν.2 ∈ X.NfinU u →
    (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u) ∈ X.K2 →
    ν.1 ∈ NOcol (X.Fu u) (Y.cs u) ρ

def RatLeviC : Prop := ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), RatLevi X u

def PsiDdC : Prop := ∀ (D : D7) (X : HidaSetting D), PsiDd X

theorem hfin_sfin {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (h : Hfin X u) :
    (h : X.B.I.Gf) ∈ SfinU X u := by
  rw [Formalism.L2.SG.PoincareInHH.Cut.sfin_iff]
  refine ⟨?_, ?_⟩
  · intro a
    have e := h.2 (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h.2 (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem gam_srat {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : X.B.I.GA) (hγ : γ ∈ Gam X u) :
    γ ∈ Srat X u := by
  obtain ⟨h1, h2⟩ := hγ
  obtain ⟨h21, h22⟩ := h2
  refine ⟨h1, Subgroup.subset_closure ⟨?_, hfin_sfin X u ⟨γ.2, h22⟩⟩⟩
  rw [Formalism.L2.SG.PoincareInHH.Cut.sinf_iff]
  intro v
  refine ⟨?_, ?_⟩
  · intro a
    have e := h21 v (X.eR a) (by simp [fixSet])
    try beta_reduce
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _
  · have e := h21 v (X.zR u) (by simp [fixSet])
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e, sub_self]
    exact Submodule.zero_mem _

theorem iotaF_coe {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (γ : Gam X u) :
    ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl

end Formalism.L2.SG.Pf.SlabCoverPf
