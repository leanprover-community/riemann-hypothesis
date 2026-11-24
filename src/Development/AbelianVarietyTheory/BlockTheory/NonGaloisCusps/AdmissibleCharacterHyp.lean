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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses

open Formalism.BasicNotions GlobalTheory.AdmLoc TensorProduct
open ReciprocityTheory.Def (H1)

variable {l : ℕ} [Fact l.Prime]

abbrev Gal (K LL : Loc.FinExt l) : Type 1 := GalData ↥(Loc.GK K) ℚ_[l] ↥LL.1 ↥(Loc.OL LL)

def Hyp (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) : Prop :=
  Standing P K LL emb Γ.lam ∧ IsTopGal (P.PD K) emb D Γ ∧ D.T1 l ∧ D.T2 l ∧ D.T3 l

def admissibleClassesTwistedChar (P : LocPrime l) (K LL : Loc.FinExt l) {n r : ℕ} (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (D : TopData n r) (Γ : Gal K LL) (c : ℕ) (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] :
    Set (H1 (twCoef (Γ.Wchi c) Γ.χ₁ X) ⊤) :=
  adm (P.PD K) emb Γ D.t D.Ut (Γ.Wchi c) X

def Stmt (P : LocPrime l) : Prop :=
  ∀ (K LL : Loc.FinExt l) (n r : ℕ) (emb : ZMod n → (↥(Loc.K0 K) →ₐ[ℚ_[l]] ↥LL.1)) (D : TopData n r)
    (Γ : Gal K LL), Hyp P K LL emb D Γ →
    ∀ c : ℕ, 2 ≤ c → c ≤ D.t →
    ∀ (X : Type) [AddCommGroup X] [Module ↥(Loc.OL LL) X] [Finite X],
      admissibleClassesTwistedChar P K LL emb D Γ c X = {0}

theorem twCoef_Wchi {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] (Γ : GalData G Qp LL O) (c : ℕ)
    (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : O ⊗[O] X) :
    twCoef (Γ.Wchi c) Γ.χ₁ X g y = (((Γ.ε g) ^ (-((c : ℤ) - 1)) : Oˣ) : O) • y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]
  | tmul a x =>
    rw [coefRep_tmul, twistRep_apply, smul_tmul']
    congr 1
    change ((Γ.χ₁⁻¹ g : Oˣ) : O) • (((Γ.chi c g : Oˣ) : O) • a) = _
    rw [smul_smul, ← Units.val_mul]
    congr 2
    simp [GalData.chi]

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses
