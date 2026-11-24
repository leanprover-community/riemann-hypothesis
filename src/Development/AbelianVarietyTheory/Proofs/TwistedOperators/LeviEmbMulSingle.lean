module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp

section Blocks

variable {n : Type} [Fintype n] [DecidableEq n]


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
omit [DecidableEq n] in
theorem _root_.GlobalTheory.InertSupp.exists_blocks (c : n → ℤ) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ n),
    ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j := by
  classical
  let S : Finset ℤ := Finset.univ.image c
  let o := S.orderIsoOfFin rfl
  let φ : n → Fin S.card := fun i => o.symm ⟨c i, Finset.mem_image_of_mem c (Finset.mem_univ i)⟩
  refine ⟨S.card, fun a => Fintype.card {i // φ i = a},
    (Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ), ?_⟩
  intro i j
  have key : ∀ x, (((Equiv.sigmaCongrRight fun a => (Fintype.equivFin {i // φ i = a}).symm).trans
      (Equiv.sigmaFiberEquiv φ)).symm x).1 = φ x := fun x => rfl
  unfold _root_.GlobalTheory.SmGL.blk
  rw [key, key]
  simp only [φ, OrderIso.lt_iff_lt, Subtype.mk_lt_mk]

variable (R : Type) [CommRing R]

def unipOf (c : n → ℤ) : Subgroup (GL n R) :=
  (unipRad R (exists_blocks c).choose_spec.choose_spec.choose).copy
    {g | ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j} (by
      ext g
      simp only [SetLike.mem_coe, CuspMax.mem_unipRad_iff_entries,
        (exists_blocks c).choose_spec.choose_spec.choose_spec, Set.mem_setOf_eq])

variable {R}


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.InertSupp.mem_unipOf {c : n → ℤ} {g : GL n R} :
    g ∈ _root_.GlobalTheory.InertSupp.unipOf R c ↔
      ∀ i j, ¬ c i < c j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j :=
  Iff.rfl

variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]


open ValuativeRel Matrix MeasureTheory in
variable {n : Type} [Fintype n] [DecidableEq n] in
variable (R : Type) [CommRing R] in
variable {R} in
variable {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] in
variable (R) in
theorem _root_.GlobalTheory.InertSupp.unipRad_eq_unipOf {e : (Σ a, m a) ≃ n}
    {c : n → ℤ} (h : ∀ i j, _root_.GlobalTheory.SmGL.blk e i < _root_.GlobalTheory.SmGL.blk e j ↔ c i < c j) :
    _root_.GlobalTheory.SmGL.unipRad R e = _root_.GlobalTheory.InertSupp.unipOf R c := by
  ext g
  rw [_root_.GlobalTheory.InertSupp.mem_unipOf, _root_.GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries]
  simp only [h]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

variable [MeasurableSpace k] [BorelSpace k]

def zetaIntegrand (Φ : Matrix n n k → ℂ) (c : GL n k → ℂ) (s : ℂ) (g : GL n k) : ℂ :=
  Φ g.val * c g * (absPow k (s + ((Fintype.card n : ℂ) - 1) / 2) (GeneralLinearGroup.det g) : ℂ)

end Local

end GlobalTheory.InertSupp
