module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1 H1)

section Triv

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O)
    (X : Type) [AddCommGroup X] [Module O X]

theorem twCoef_chi_one (g : G) (m : O ⊗[O] X) : twCoef (Γ.Wchi 1) Γ.χ₁ X g m = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [coefRep_tmul, twistRep_apply]
    congr 1
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • ((Γ.chi 1 g : O) • a) = a
    rw [GalData.chi_one, smul_smul]
    simp
  | add a b ha hb => rw [map_add (f := _), ha, hb]

def homModInertia (I : Subgroup G) : Set (H1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤) :=
  {c | ∃ z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤), Submodule.Quotient.mk z = c ∧
    ∀ g ∈ I, (z : G → O ⊗[O] X) g = 0}

theorem cocycle_add (z : ↥(Z1 (twCoef (Γ.Wchi 1) Γ.χ₁ X) ⊤)) (g h : G) :
    (z : G → O ⊗[O] X) (g * h) = (z : G → O ⊗[O] X) g + (z : G → O ⊗[O] X) h := by
  rw [cocycle_mul z g h, twCoef_chi_one]

theorem homModInertia_eq_unr (I : Subgroup G) :
    homModInertia Γ X I = (unr (twCoef (Γ.Wchi 1) Γ.χ₁ X) I : Set _) := by
  ext c
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  constructor
  · rintro ⟨z', hz, h⟩
    rw [← hz]
    exact (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z').mpr h
  · intro h
    exact ⟨z, rfl, (mk_mem_unr_of_trivial (twCoef_chi_one Γ X) I z).mp h⟩

end Triv

def AdmChiOneUnramified {l : ℕ} [Fact l.Prime] (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)),
    Standing P K LL emb Γ.lam → IsTopGal (P.PD K) emb D Γ → D.T1 l → D.T2 l → D.T3 l →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi 1) X = homModInertia Γ X (Loc.IK K)

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified
