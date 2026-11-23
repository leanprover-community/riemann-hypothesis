module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleModuleSheafMapMonoEpiIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC UpperTheory.Pbf

private def sumP (P₁ P₂ : PSh) : PSh where
  obj U := P₁.obj U ⊕ P₂.obj U
  map h := TypeCat.ofHom (Sum.map (P₁.map h) (P₂.map h))
  map_id U := by
    ext x
    rcases x with x | x <;> simp
  map_comp a b := by
    ext x
    rcases x with x | x <;> simp

private def sumD {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q) : sumP P₁ P₂ ⟶ Q where
  app U := TypeCat.ofHom (Sum.elim (f.app U) (g.app U))
  naturality U V k := by
    ext x
    rcases x with x | x
    · exact congrFun (congrArg (fun t => t.hom) (f.naturality k)) x
    · exact congrFun (congrArg (fun t => t.hom) (g.naturality k)) x

theorem UpperTheory.epi_freeBiprodDesc_of_zariskiLocally_surjective :
    ∀ (R : Type) [CommRing R] {P₁ P₂ Q : PSh} (f : P₁ ⟶ Q) (g : P₂ ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V h => (∃ x, f.app (op V) x = Q.map h.op y) ∨ ∃ x, g.app (op V) x = Q.map h.op y) → Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  intro R _ P₁ P₂ Q f g h
  have mc : ∀ {P : PSh} (c : P ⟶ Q) {M : Shv R} (p : (free R).obj Q ⟶ M) (T : Scheme.{0})
      (x : P.obj (op T)),
      Sec.map ((free R).map c ≫ p) (freeGen R P T x) = Sec.map p (freeGen R Q T (c.app (op T) x)) := by
    intro P c M p T x
    have h4 := (GlobalTheory.T.free_sections_ext_res_map R P M).2.2.2 Q c T x
    show Sec.map p (Sec.map ((free R).map c) (freeGen R P T x)) = _
    rw [h4]
  have hE : Epi ((free R).map (sumD f g)) := by
    apply (GlobalTheory.T.freeEtaleModuleSheaf_map_mono_epi_iso R (sumD f g)).2.1
    intro T y
    obtain ⟨S, hS, hP⟩ := h T y
    refine ⟨S, hS, fun W k hk => ?_⟩
    rcases hP W k hk with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact ⟨Sum.inl x, hx⟩
    · exact ⟨Sum.inr x, hx⟩
  constructor
  intro Z u v huv
  have ha : (free R).map f ≫ u = (free R).map f ≫ v := by
    simpa using congrArg (biprod.inl ≫ ·) huv
  have hb : (free R).map g ≫ u = (free R).map g ≫ v := by
    simpa using congrArg (biprod.inr ≫ ·) huv
  rw [← cancel_epi ((free R).map (sumD f g))]
  apply (GlobalTheory.T.free_sections_ext_res_map R (sumP P₁ P₂) Z).2.1
  intro T z
  rw [mc, mc]
  cases z with
  | inl x =>
    have e := mc f u T x
    have e' := mc f v T x
    rw [ha] at e
    exact e.symm.trans e'
  | inr x =>
    have e := mc g u T x
    have e' := mc g v T x
    rw [hb] at e
    exact e.symm.trans e'
