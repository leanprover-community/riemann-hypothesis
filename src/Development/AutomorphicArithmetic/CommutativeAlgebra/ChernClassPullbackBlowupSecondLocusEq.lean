module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.LineUnitTrivialization

private def arr {a : Act} {E : Spc} {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) : a.G.obj Γ(U, ⊤) :=
  (show ComposableArrows (Ob a Γ(U, ⊤)) 1 from x.2).hom.1

private theorem det_scalar {A : Type} [CommRing A] (u : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp

private theorem lineUnit_line {a : Act} {E : Spc} (χ : a.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (arr x)) :=
  det_scalar _

private theorem lineUnit_map {a b : Act} {E : Spc} (φ : Act.Hom a b) (χ : b.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.map E φ ≫ Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (φ.g.app Γ(U, ⊤) (arr x))) :=
  det_scalar _

private def chiM (N : ℕ) (Q : Pred (BC N)) : ((BC N).sub Q).G ⟶ gmF where
  app A := GrpCat.ofHom (MonoidHom.snd Aˣ Aˣ / MonoidHom.fst Aˣ Aˣ)
  naturality A B f := by
    ext x
    exact (map_div (Units.map (f.hom : A →* B)) x.2 x.1).symm

private theorem isUnit_um_join_of_span_castSucc_eq_whole {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A)
    (h : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤) : IsUnit (x.2.1 0) := by
  have h' : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) ≤ Ideal.span {x.2.1 0} := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Um.join, Fin.snoc_castSucc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [h, top_le_iff, Ideal.span_singleton_eq_top] at h'
  exact h'

private def sU {N : ℕ} {A : CommRingCat.{0}} (y : ((BC N).sub ((Q2 N).comap (βC N))).D.obj A) : Aˣ :=
  (isUnit_um_join_of_span_castSucc_eq_whole (A := A) y.1 y.2).unit

private def wS (N : ℕ) (E : Spc) (T : Scheme.{0}) (y : Sx (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) 0 T) : (Γ(T, ⊤))ˣ :=
  sU (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 0 from y.2).left.pt

private theorem triv (N : ℕ) (E : Spc) :
    IsTrivBy (Sp.line E (chiM N ((Q2 N).comap (βC N)))) (wS N E) := by
  refine ⟨?_, ?_⟩
  · intro T' T g x
    apply Units.ext
    simp only [wS, sU, IsUnit.unit_spec, Units.coe_map]
    rfl
  · intro T x
    rw [lineUnit_line]
    apply Units.ext
    have key := (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 1 from x.2).hom.2
    have k2 := congrArg (fun y => (y.1.2.1 0 : Γ(T, ⊤))) key
    simp only [wS, sU, IsUnit.unit_spec]
    exact k2.symm

end UpperTheory.LineUnitTrivialization

end

open UpperTheory.LineUnitTrivialization in
theorem UpperTheory.chernClass_pullback_blowupSecondLocus_eq :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) =
          pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiH N))) := by
  intro q _ N E hE
  have hI : Inv q (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hI' : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  obtain ⟨-, hpull, hadd⟩ := GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q
  rw [hpull _ _ hI', hpull _ _ hI']
  have h0 : c1 q (Sp.line E (chiM N ((Q2 N).comap (βC N)))) = 0 := UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ _ hI (triv N E)
  have hsum := hadd (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiH N))
    (Sp.line E (chiM N ((Q2 N).comap (βC N))))
    (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiB N)) hI (by
      intro U x
      rw [lineUnit_map, lineUnit_map, lineUnit_line]
      first
        | exact (mul_div_cancel _ _).symm
        | exact (mul_div_cancel_left _ _).symm
        | exact (mul_div_cancel'_right _ _).symm)
  rw [hsum, h0, add_zero]
