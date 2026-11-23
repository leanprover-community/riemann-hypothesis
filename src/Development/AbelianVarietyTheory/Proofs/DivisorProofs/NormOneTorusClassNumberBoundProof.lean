module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleQuadraticExistsUnitEqMulSg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

namespace GlobalTheory.UCls

theorem torusBound : TorusBound := by
  intro E _ _ _ r M G Λ hr hM hE hΛ
  classical
  set c := IsCMField.complexConj E
  obtain ⟨S, hS, hS'⟩ := GlobalTheory.UCls.normOne_classes_le_classNumber E hE
  obtain ⟨S', hS₂, hS₂'⟩ := GlobalTheory.UCls.NormOneMod.normOne_mod E M hM
  let T : Finset (RA (maximalRealSubfield E) E) := (S ×ˢ S').image fun p => p.1 * p.2
  have hT : T.card ≤ classNumber E * M ^ (2 * fdeg E) :=
    Finset.card_image_le.trans ((Finset.card_product S S').le.trans (Nat.mul_le_mul hS hS₂))
  have hTA : ∀ a b : RA (maximalRealSubfield E) E, IsTA c a → IsTA c b → IsTA c (a * b) := by
    intro a b ha hb
    unfold IsTA at *
    rw [map_mul, mul_mul_mul_comm, ha, hb, one_mul]
  have hone : IsTA c (1 : RA (maximalRealSubfield E) E) := by simp [IsTA]
  let Q := Quot fun a b : {t // IsTA c t} => TEquiv c G (Λ : Set (Fin r → E)) M a.1 b.1
  let φ : T → Q := fun x => if h : IsTA c x.1 then Quot.mk _ ⟨x.1, h⟩ else Quot.mk _ ⟨1, hone⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, u, hu, k, hk, hkint, hsTA, rfl⟩ := hS' t ht
    obtain ⟨s', hs', hs'TA, k', hk'TA, hk'1, rfl⟩ := hS₂' k hk hkint
    obtain ⟨g, hg, hdet⟩ := GlobalTheory.UCls.Det.exists_isKM_det_eq E hE r M G Λ hr hM hΛ k' hk'TA hk'1
    have hmem : s * s' ∈ T := Finset.mem_image.2 ⟨(s, s'), Finset.mem_product.2 ⟨hs, hs'⟩, rfl⟩
    refine ⟨⟨s * s', hmem⟩, ?_⟩
    simp only [φ, dif_pos (hTA s s' hsTA hs'TA)]
    refine Quot.sound ⟨u, hu, g, hg, ?_⟩
    rw [hdet]
    ring
  calc torusNo c G (Λ : Set (Fin r → E)) M = ENat.card Q := rfl
    _ ≤ ENat.card T := ENat.card_le_card_of_injective (Function.injective_surjInv hφ)
    _ = T.card := by rw [ENat.card_eq_coe_fintype_card, Fintype.card_coe]
    _ ≤ _ := by exact_mod_cast hT

end GlobalTheory.UCls
