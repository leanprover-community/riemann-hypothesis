module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise

noncomputable section

namespace GlobalTheory.UnitSplit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem mt_mul (S : HSp D) (g g' : GA D S) : mt S (g * g') = mt S g * mt S g' := by
  simp [Formalism.L2.Theta.mt]

theorem mt_one (S : HSp D) : mt S 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem eq_of_parts {A : Type*} [CommRing A] {e f m m' o : A} (k1 : (e + f) * (m - o) = m - o)
    (k2 : (e + f) * (m' - o) = m' - o) (k3 : e * m = e * m') (k4 : f * m' = f * m) : m = m' := by
  linear_combination (-1 : A) * k1 + k2 + k3 - k4

theorem mt_unit (S : HSp D) (g : GA D S) :
    ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g = (HSpace.gram S).map (incA D) := g.2

theorem gram_mul_conj_inv (S : HSp D) (e : AE D) (g : GA D S) :
    (HSpace.gram S).map (incA D) * (cA D e • mt S g⁻¹) =
      ((e • mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
  have hu := mt_unit S g
  have h1 : mt S g * mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hmap : (e • mt S g).map (cA D) = cA D e • (mt S g).map (cA D) := by
    ext i j; simp [Matrix.map_apply, map_mul]
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  calc (HSpace.gram S).map (incA D) * mt S g⁻¹
      = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) * mt S g * mt S g⁻¹ := by rw [hu]
    _ = ((mt S g).map (cA D)).transpose * (HSpace.gram S).map (incA D) := by
        rw [Matrix.mul_assoc _ (mt S g), h1, Matrix.mul_one]

theorem eq_of_split_part : ∀ (D : D7) (S : HSp D) (e : AE D) (h h' : GA D S), IsSplitIdem D e → SuppAt e S h →
    SuppAt e S h' → (∀ i j, e * Formalism.L2.Theta.mt S h i j = e * Formalism.L2.Theta.mt S h' i j) → h = h' := by
  intro D S e h h' _ hs hs' hee
  have hJu : IsUnit ((HSpace.gram S).map (incA D)).det := by
    have hd : ((HSpace.gram S).map (incA D)).det = incA D (HSpace.gram S).det := by
      rw [RingHom.map_det]; rfl
    rw [hd]; exact (gram_isUnit_det S).map _
  have hE : e • mt S h = e • mt S h' := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul]; exact hee i j
  have hN : cA D e • mt S h⁻¹ = cA D e • mt S h'⁻¹ := by
    have h2 := (gram_mul_conj_inv S e h).trans
      ((congrArg (fun X : Matrix (Fin S.rank) (Fin S.rank) (AE D) => (X.map (cA D)).transpose * (HSpace.gram S).map (incA D)) hE).trans
        (gram_mul_conj_inv S e h').symm)
    have h3 := congrArg (fun X => ((HSpace.gram S).map (incA D))⁻¹ * X) h2
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul] using h3
  have a1 : mt S h⁻¹ * mt S h = 1 := by rw [← mt_mul, inv_mul_cancel, mt_one]
  have a2 : mt S h' * mt S h'⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  have hM : cA D e • mt S h' = cA D e • mt S h := by
    calc cA D e • mt S h' = cA D e • (mt S h' * mt S h⁻¹ * mt S h) := by
          rw [Matrix.mul_assoc, a1, Matrix.mul_one]
      _ = mt S h' * (cA D e • mt S h⁻¹) * mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul]
      _ = mt S h' * (cA D e • mt S h'⁻¹) * mt S h := by rw [hN]
      _ = cA D e • mt S h := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, a2, Matrix.one_mul]
  have hMM : mt S h = mt S h' := by
    ext i j
    have k1 := hs i j
    have k2 := hs' i j
    have k3 := hee i j
    have k4 : cA D e * mt S h' i j = cA D e * mt S h i j := by
      have := congrFun (congrFun hM i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at this; exact this
    simp only [Matrix.sub_apply] at k1 k2
    exact eq_of_parts k1 k2 k3 k4
  exact Subtype.ext (Units.ext hMM)

end GlobalTheory.UnitSplit

end
