module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivLiftResiduePadicAlgClStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingEquivExtendingOfKerLeStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

namespace GlobalTheory.ResidueLift

open IsLocalRing

theorem res_eq_zero_iff {l : ℕ} [Fact l.Prime] (x : GlobalTheory.ZJ.OO l) :
    residue (GlobalTheory.ZJ.OO l) x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.ZH.not_isUnit_OO_iff]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (L : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] L] (J : Type) (a b : J → PadicAlgCl l), (∀ j, ‖a j‖ ≤ 1) → (∀ j, ‖b j‖ ≤ 1) → (∀ p : MvPolynomial J (PadicAlgCl l), (∀ n, p.coeff n ∈ L ∧ ‖p.coeff n‖ ≤ 1) → (‖MvPolynomial.eval a p‖ < 1 ↔ ‖MvPolynomial.eval b p‖ < 1)) → ∃ g : PadicAlgCl l ≃ₐ[L] PadicAlgCl l, ∀ j, ‖g (a j) - b j‖ < 1 := by
  intro l _ L _ J a b ha hb hab
  let K := PadicAlgCl l
  let O := GlobalTheory.ZJ.OO l
  let a' : J → O := fun j => ⟨a j, (GlobalTheory.ZH.mem_OO_iff _).2 (ha j)⟩
  let b' : J → O := fun j => ⟨b j, (GlobalTheory.ZH.mem_OO_iff _).2 (hb j)⟩
  let As : Subring O := L.toSubalgebra.toSubring.comap O.subtype
  let f : As →+* GlobalTheory.ZJ.kb l := (residue O).comp As.subtype
  let R := f.range
  have key : ∀ (c : J → O) (q : MvPolynomial J As),
      MvPolynomial.aeval (fun j => residue O (c j)) (MvPolynomial.map f.rangeRestrict q) = 0 ↔
      ‖MvPolynomial.eval (fun j => (c j : K)) (MvPolynomial.map (O.subtype.comp As.subtype) q)‖ < 1 := by
    intro c q
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval_map]
    have h1 : MvPolynomial.eval₂ ((algebraMap R (GlobalTheory.ZJ.kb l)).comp f.rangeRestrict) (fun j => residue O (c j)) q
        = residue O (MvPolynomial.eval₂ As.subtype c q) := by
      rw [MvPolynomial.eval₂_comp_left]; rfl
    have h2 : MvPolynomial.eval₂ (O.subtype.comp As.subtype) (fun j => (c j : K)) q
        = ((MvPolynomial.eval₂ As.subtype c q : O) : K) :=
      (MvPolynomial.eval₂_comp_left O.subtype As.subtype c q).symm
    rw [h1, h2, res_eq_zero_iff]
  have hII : ∀ p : MvPolynomial J R, MvPolynomial.aeval (fun j => residue O (a' j)) p = 0 →
      MvPolynomial.aeval (fun j => residue O (b' j)) p = 0 := by
    intro p hp
    obtain ⟨q, rfl⟩ := MvPolynomial.map_surjective f.rangeRestrict f.rangeRestrict_surjective p
    rw [key] at hp ⊢
    refine (hab _ fun n => ?_).1 hp
    rw [MvPolynomial.coeff_map]
    exact ⟨(AddMonoidAlgebra.coeff q n).2, (GlobalTheory.ZH.mem_OO_iff _).1 (((AddMonoidAlgebra.coeff q n : As) : O).2)⟩
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := l)
  obtain ⟨φ, hφR, hφ⟩ := GlobalTheory.T.exists_ringEquiv_extending_of_ker_le' _ GlobalTheory.ZJ.exists_pow_eq_one_kb R J _ _ hII
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_algEquiv_lift_residue_padicAlgCl l L φ fun x hx => hφR _ ⟨⟨x, hx⟩, rfl⟩
  exact ⟨g, fun j => hg (a' j) (b' j) (hφ j).symm⟩

end GlobalTheory.ResidueLift
