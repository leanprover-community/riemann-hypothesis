module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EqvTwistBlowupRestriction
public import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.BlowEqvInter

private theorem pb_sub (E : Spc) {a : Act} (Q R S : Pred a) (h1 : Q.Le R) (h2 : Q.Le S)
    (h : ∀ A x, R.P A x → S.P A x → Q.P A x) :
    IsPullback (Sp.map E (inclLe h1)) (Sp.map E (inclLe h2)) (Sp.map E (incl R)) (Sp.map E (incl S)) := by
  refine stackProduct_isPullback_of_actionPullback E (inclLe h1) (inclLe h2) (incl R) (incl S) ?_ ?_ ?_ ?_
  · intro A z
    rfl
  · intro A z
    rfl
  · intro A x y hxy
    have hy : S.P A x.1 := by
      have : (x.1 : a.D.obj A) = y.1 := hxy
      rw [this]
      exact y.2
    refine ⟨⟨x.1, h A x.1 x.2 hy⟩, ⟨rfl, ?_⟩, ?_⟩
    · exact Subtype.ext hxy
    · rintro z ⟨hz1, -⟩
      subst hz1
      rfl
  · intro A g k hgk
    refine ⟨g, ⟨rfl, hgk⟩, ?_⟩
    rintro z ⟨hz1, -⟩
    exact hz1

private theorem comm_sub (E : Spc) {a b : Act} (φ : Act.Hom a b) (Q R : Pred b) (h : Q.Le R)
    (h' : (Q.comap φ).Le (R.comap φ)) :
    Sp.map E (φ.sub Q) ≫ Sp.map E (inclLe h) = Sp.map E (inclLe h') ≫ Sp.map E (φ.sub R) := by
  rfl

end UpperTheory.BlowEqvInter

open UpperTheory.BlowEqvInter in
theorem UpperTheory.pullback_cube_faces_equiv_tate_twist :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (i : ℤ) (h₁ h₂), Inv q E →
        Eqv _ (pullback.map (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N))))
          (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) (Sp.map E ((βC N).sub (Q1 N))) (Sp.map E ((βC N).sub (Q2 N)))
          (Sp.map E (βC N)) h₁ h₂) (tw q i) := by
  intro q _ N E i h₁ h₂ hE
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hP := pb_sub E ((Q1 N).inf (Q2 N)) (Q1 N) (Q2 N) (fun A x hx => hx.1) (fun A x hx => hx.2)
    (fun A x ha hb => ⟨ha, hb⟩)
  have hP' := pb_sub E (((Q1 N).inf (Q2 N)).comap (βC N)) ((Q1 N).comap (βC N)) ((Q2 N).comap (βC N))
    (fun A x hx => hx.1) (fun A x hx => hx.2) (fun A x ha hb => ⟨ha, hb⟩)
  have hb := eqv_twist_blowupRestriction q N E ((Q1 N).inf (Q2 N)) i (fun A x hx => hx.2) hE
  set_option synthInstance.maxHeartbeats 200000 in
   have e : hP'.isoPullback.hom ≫ pullback.map _ _ _ _ _ _ _ h₁ h₂ =
      Sp.map E ((βC N).sub ((Q1 N).inf (Q2 N))) ≫ hP.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pullback.map, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_fst]
      exact (comm_sub E (βC N) _ _ _ _).symm
    · simp only [pullback.map, Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
        IsPullback.isoPullback_hom_snd]
      exact (comm_sub E (βC N) _ _ _ _).symm
  refine (hcomp _ _ _ hP'.isoPullback.hom _).2.1 (hiso _ _ hP'.isoPullback.hom inferInstance) ?_
  rw [e]
  exact (hcomp _ _ _ _ _).1 hb (hiso _ _ _ inferInstance)
