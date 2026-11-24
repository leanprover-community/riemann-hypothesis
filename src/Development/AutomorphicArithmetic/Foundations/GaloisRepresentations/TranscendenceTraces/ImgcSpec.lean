module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces.RepresentationImage

variable {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}

private theorem img_zero (τ : Fam p I J) (n : ℤ) :
    τ.IsImage (0 : Cochain ((chains R').obj (sch.obj Z)) I n) (0 : Cochain ((chains R).obj (sch.obj S)) J n) := by
  intro k s h A
  have h1 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj S) (I := J) (n := n)).1 0 0 k s h A.U A.u).2.2.1
  have h2 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R' (E := sch.obj Z) (I := I) (n := n)).1 0 0 k s h A.V A.v).2.2.1
  exact h1.trans ((map_zero ((τ.deg s).app A)).symm.trans (congrArg ((τ.deg s).app A) h2.symm))

private theorem img_add (τ : Fam p I J) {n : ℤ} {a a' : Cochain ((chains R').obj (sch.obj Z)) I n}
    {b b' : Cochain ((chains R).obj (sch.obj S)) J n} (h : τ.IsImage a b) (h' : τ.IsImage a' b') :
    τ.IsImage (a + a') (b + b') := by
  intro k s hs A
  rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 b b' k s hs A.U A.u).1, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R').1 a a' k s hs A.V A.v).1, map_add (f := _),
    h k s hs A, h' k s hs A]

private noncomputable def imgc (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : Cocycle ((chains R).obj (sch.obj S)) J n :=
  Cocycle.mk ((hI R' R τ n).1 α.1).exists.choose (n + 1) rfl (by
    have h := (hI R' R τ n).2 (n + 1) rfl _ _ ((hI R' R τ n).1 α.1).exists.choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact ((hI R' R τ (n + 1)).1 0).unique h (img_zero τ (n + 1)))

private theorem imgc_spec (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : τ.IsImage α.1 (imgc hI τ α).1 :=
  ((hI R' R τ n).1 α.1).exists.choose_spec

private theorem imgc_eq (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : imgc hI τ α = β :=
  Cocycle.ext (((hI R' R τ n).1 α.1).unique (imgc_spec hI τ α) h)

private noncomputable def opMap (hI : ImgBasic) (τ : Fam p I J) (n : ℤ) :
    CohomologyClass ((chains R').obj (sch.obj Z)) I n →+ CohomologyClass ((chains R).obj (sch.obj S)) J n :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc hI τ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq hI τ _ _ (img_add τ (imgc_spec hI τ α) (imgc_spec hI τ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb, -⟩ := (hI R' R τ n').1 a'
      exact ⟨n', hn', b, ((hI R' R τ n).1 _).unique ((hI R' R τ n').2 n hn' _ _ hb) (imgc_spec hI τ ⟨_, ha⟩)⟩)

private theorem op_spec (hI : ImgBasic) (τ : Fam p I J) (n : ℤ)
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : τ.op n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : CohomologyClass ((chains R').obj (sch.obj Z)) I n →+
      CohomologyClass ((chains R).obj (sch.obj S)) J n =>
    ∀ (α : Cocycle _ I n) (β : Cocycle _ J n), τ.IsImage α.1 β.1 →
      c (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap hI τ n, fun α β h => congrArg CohomologyClass.mk (imgc_eq hI τ α β h)⟩ α β h

end UpperTheory.Gal.TranscendenceTraces.RepresentationImage

open UpperTheory.Gal.TranscendenceTraces.RepresentationImage in
theorem UpperTheory.Gal.TranscendenceTraces.rpOp_of :
    ImgBasic → RpOp := by
  intro hI Z S p R' R _ _ I J τ n x a hx
  obtain ⟨α, rfl, rfl⟩ := hx
  exact ⟨imgc hI τ α, (op_spec hI τ n α _ (imgc_spec hI τ α)).symm, imgc_spec hI τ α 0 n (by simp) (Sq.self p)⟩
