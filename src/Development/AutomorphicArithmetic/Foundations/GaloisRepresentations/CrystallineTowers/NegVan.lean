module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.Seam

private theorem H_subsingleton_of_neg (R : Type) [CommRing R] (E : Spc) (F : Shv R) {n : ℤ} (hn : n < 0) :
    Subsingleton (H R E F n) := by
  haveI hK : ((chains R).obj E).IsStrictlyLE 0 :=
    (inferInstance : CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)
  haveI hL : (res R F).IsStrictlyGE 0 := by
    dsimp [res]
    infer_instance
  have hz : ∀ z : Cochain ((chains R).obj E) (res R F) n, z = 0 := by
    intro z
    apply Cochain.ext
    intro p q hpq
    by_cases hp : 0 < p
    · exact (CochainComplex.isZero_of_isStrictlyLE ((chains R).obj E) 0 p hp).eq_of_src _ _
    · exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q (by omega)).eq_of_tgt _ _
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨y, rfl⟩ := CohomologyClass.mk_surjective b
  congr 1
  apply Subtype.ext
  rw [hz x.1, hz y.1]

theorem UpperTheory.Gal.Seam.negVan :
    NegVan := by
  intro l _ X n hn
  haveI : ∀ k : ℕ, Subsingleton (HtL l k (sch.obj X) n 0) := fun k =>
    H_subsingleton_of_neg (ZMod (l ^ k)) (sch.obj X) (tw (l ^ k) 0) hn
  haveI : Subsingleton (Hl l (sch.obj X) n 0) := by
    dsimp only [Hl]
    infer_instance
  dsimp only [HQ]
  infer_instance
