module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S
open scoped TensorProduct

def eqvFn {G : Type} [Group G] (Γ K : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V]
    (a : Γ →* Module.End ℂ V) (ψ : K →* ℂˣ) : Submodule ℂ (G → V) where
  carrier := {φ | ∀ (γ : Γ) (x : G) (κ : K), φ (γ * x * κ) = ((ψ κ)⁻¹ : ℂˣ) • a γ (φ x)}
  add_mem' := by
    intro φ φ' h h' γ x κ
    simp only [Pi.add_apply, map_add (f := _), smul_add, h γ x κ, h' γ x κ]
  zero_mem' := by
    intro γ x κ
    simp
  smul_mem' := by
    intro c φ h γ x κ
    simp only [Pi.smul_apply, map_smul, h γ x κ]
    rw [smul_comm]

abbrev GAf (D : D7) : Type :=
  letI := D.host.cmStar
  ↥(Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def GF (D : D7) : Subgroup (GAf D) :=
  letI := D.host.cmStar
  (Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)).subgroupOf
    (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def KPi (D : D7) (Lv : LevelData D) (u : D.what₂.Word) : Subgroup (GAf D) :=
  letI := D.host.cmStar
  (Lv u).U.subgroupOf
    (Formalism.UG.UPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def colFn (D : D7) (Lv : LevelData D) (u : D.what₂.Word) (V : Type) [AddCommGroup V] [Module ℂ V]
    (a : GF D →* Module.End ℂ V) (ψ : KPi D Lv u →* ℂˣ) : Submodule ℂ (GAf D → V) :=
  eqvFn (GF D) (KPi D Lv u) V a ψ

structure ColRep (D : D7) (Lv : LevelData D) (u : D.what₂.Word) where
  H : D.what₂.Tau → Type
  [nacg : ∀ ρ, NormedAddCommGroup (H ρ)]
  [ips : ∀ ρ, InnerProductSpace ℂ (H ρ)]
  π : ∀ ρ, Matrix (Fin D.R.k) (Fin D.R.k) ℂ → (H ρ →L[ℂ] H ρ)
  π_type : ∀ ρ, IsHCTypeU D.R.k (uColR D u ρ) (π ρ)
  B : D.what₂.Tau → Matrix (Fin D.R.k) (Fin D.R.k) ℂ
  B_spec : letI := D.host.cmStar; ∀ ρ, (B ρ).conjTranspose * B ρ = D.sp.gram0.map (embOf D ρ)
  a : GF D →* Module.End ℂ (⨂[ℂ] ρ, H ρ)
  a_spec : ∀ (γ : GF D) (γ0 : GL (Fin D.R.k) D.host.E),
    (γ : GAf D).1 = Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F)
      (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ0 →
    ∀ v : ∀ ρ, H ρ, a γ (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ
      (fun ρ => π ρ (B ρ * (γ0 : Matrix (Fin D.R.k) (Fin D.R.k) D.host.E).map (embOf D ρ) * (B ρ)⁻¹) (v ρ))
  ψ : KPi D Lv u →* ℂˣ

attribute [instance] ColRep.nacg ColRep.ips

abbrev ColRep.V {D : D7} {Lv : LevelData D} {u : D.what₂.Word} (X : ColRep D Lv u) : Type := ⨂[ℂ] ρ, X.H ρ

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.StandardLattice
