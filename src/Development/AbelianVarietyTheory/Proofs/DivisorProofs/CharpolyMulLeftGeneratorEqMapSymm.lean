module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.RingTheory.Adjoin.PowerBasis

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory

theorem charpoly_mulLeft_eq_of_adjoin_eq_top {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (u : A) (P : F[X]) (hP : P.Monic) (hadj : Algebra.adjoin F {u} = ⊤)
    (hu : aeval u P = 0) (hdim : Module.finrank F A = P.natDegree) :
    (LinearMap.mulLeft F u).charpoly = P := by
  have hint : IsIntegral F u := ⟨P, hP, hu⟩
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = u := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hmin : minpoly F u = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd F u hu) ?_).symm
    rw [← hdim, pb.finrank, PowerBasis.ofAdjoinEqTop_dim]
  have h1 := charpoly_leftMulMatrix pb
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, hmin] at h1
  exact h1

theorem charpoly_mulLeft_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  intro K B R _ e u Q hQ hadj hu hdim
  exact charpoly_mulLeft_eq_of_adjoin_eq_top u _ (hQ.map _) hadj hu (by rw [hdim, hQ.natDegree_map])

end GlobalTheory
