module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTwoMulRhoSubTr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartProjectionMatrixMapMulVecOfEigenvector
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply

@[expose] public section

open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal

theorem _root_.GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig  <;> assumption)
