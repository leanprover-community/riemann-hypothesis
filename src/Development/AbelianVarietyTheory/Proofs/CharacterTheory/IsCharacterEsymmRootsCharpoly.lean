module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def compoundRep {G : Type} [Group G] {n : ℕ} (j : ℕ) (ρ : G →* GL (Fin n) ℂ) :
    Representation ℂ G (Set.powersetCard (Fin n) j → ℂ) where
  toFun g := Matrix.toLin' (GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ))
  map_one' := by
    rw [map_one, Units.val_one, GlobalTheory.compoundMatrix_one, Matrix.toLin'_one]; rfl
  map_mul' a b := by
    rw [map_mul, Units.val_mul, GlobalTheory.compoundMatrix_mul, Matrix.toLin'_mul]; rfl

open Polynomial in
private lemma det_submatrix_subsetEnum_eq_det_submatrix_val {n j : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Set.powersetCard (Fin n) j) :
    (A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S)).det =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).det := by
  have hmem : ∀ i, _root_.GlobalTheory.subsetEnum S i ∈ S.1 := fun i => by
    have : _root_.GlobalTheory.subsetEnum S i ∈ Set.range (_root_.GlobalTheory.subsetEnum S) :=
      ⟨i, rfl⟩
    rw [_root_.GlobalTheory.range_subsetEnum] at this
    exact_mod_cast this
  let σ : Fin j ≃ {x // x ∈ S.1} := Equiv.ofBijective
    (fun i => ⟨_root_.GlobalTheory.subsetEnum S i, hmem i⟩)
    ⟨fun a b hab => _root_.GlobalTheory.subsetEnum_injective S (congrArg Subtype.val hab),
      fun x => by
        have hx : x.1 ∈ ((S.1 : Finset (Fin n)) : Set (Fin n)) := x.2
        rw [← _root_.GlobalTheory.range_subsetEnum] at hx
        obtain ⟨i, hi⟩ := hx
        exact ⟨i, Subtype.ext hi⟩⟩
  have hsub : A.submatrix (_root_.GlobalTheory.subsetEnum S) (_root_.GlobalTheory.subsetEnum S) =
      (A.submatrix (Subtype.val : {x // x ∈ S.1} → Fin n) Subtype.val).submatrix σ σ := rfl
  rw [hsub, Matrix.det_submatrix_equiv_self]

open Polynomial in
private lemma trace_compoundMatrix_eq_sum_principal_minors {n : ℕ} (j : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (_root_.GlobalTheory.compoundMatrix j A).trace = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (A.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  rw [Finset.sum_subtype (p := fun s : Finset (Fin n) => s ∈ Set.powersetCard (Fin n) j) _
    (fun s => by simp [Finset.mem_powersetCard, Set.powersetCard])]
  unfold _root_.GlobalTheory.compoundMatrix
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply]
  exact Finset.sum_congr rfl fun S _ => det_submatrix_subsetEnum_eq_det_submatrix_val A S

open Polynomial in
private lemma esymm_roots_charpoly_eq_sum_principal_minors {n : ℕ} (j : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    M.charpoly.roots.esymm j = ∑ s ∈ Finset.powersetCard j Finset.univ,
      (M.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
  have hdeg : M.charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hcard : M.charpoly.roots.card = M.charpoly.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  rcases le_or_gt j n with hj | hj
  · have h1 := coeff_eq_esymm_roots_of_card hcard (k := n - j) (by omega)
    have h2 := M.charpoly_coeff_eq_sum_minors j (by simp [hj])
    rw [hdeg, Nat.sub_sub_self hj, M.charpoly_monic.leadingCoeff, one_mul] at h1
    rw [Fintype.card_fin, h1] at h2
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h2
  · rw [Finset.powersetCard_eq_empty.mpr (by simp [hj]), Finset.sum_empty, Multiset.esymm,
      Multiset.powersetCard_eq_empty _ (by omega)]
    simp


open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_esymm_roots_charpoly :
    ∀ (G : Type) [Group G] (n j : ℕ) (ρ : G →* GL (Fin n) ℂ), _root_.GlobalTheory.BI.IsChar ℂ ℂ
      (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) := by
  intro G _ n j ρ
  have h := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (_root_.GlobalTheory.BI.compoundRep j ρ)).1
  have heq : (fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots.esymm j) =
      fun g => algebraMap ℂ ℂ ((_root_.GlobalTheory.BI.compoundRep j ρ).character g) := by
    funext g
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change _ = LinearMap.trace ℂ _
      (Matrix.toLin' (_root_.GlobalTheory.compoundMatrix j (ρ g : Matrix (Fin n) (Fin n) ℂ)))
    rw [Matrix.trace_toLin'_eq, trace_compoundMatrix_eq_sum_principal_minors, esymm_roots_charpoly_eq_sum_principal_minors]
  rw [heq]
  exact h

end GlobalTheory.BI
