module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Vanishing
open GlobalTheory.ShFam.BdArc (IsHolPts)

namespace GlobalTheory.CuspDim.IsoPow

variable {Z : Scheme.{0}} {B : LB Z}

theorem res_res {U V W : Z.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(Z, U)ˣ) :
    res h' (res h u) = res (h'.trans h) u := by
  ext
  change (Z.presheaf.map (homOfLE h).op ≫ Z.presheaf.map (homOfLE h').op).hom u.val = _
  rw [← Functor.map_comp]
  rfl

theorem pow_le (n : ℕ) (j : PUnit → B.ι) : (lbPow B n).U j ≤ B.U (j PUnit.unit) :=
  LB.wchart_le B (fun _ => 𝟙 Z) j PUnit.unit

theorem res_pow_g (n : ℕ) (j j' : PUnit → B.ι) {W : Z.Opens} (h : W ≤ (lbPow B n).U j ⊓ (lbPow B n).U j') :
    res h ((lbPow B n).g j j') =
      res (h.trans (inf_le_inf (pow_le n j) (pow_le n j'))) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
  have e : (lbPow B n).g j j' =
      res (inf_le_inf (pow_le n j) (pow_le n j')) (B.g (j PUnit.unit) (j' PUnit.unit)) ^ (n : ℤ) :=
    Fintype.prod_unique fun a : PUnit.{1} => res (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => 𝟙 Z) j a))
      (inf_le_right.trans (LB.wchart_le B (fun _ => 𝟙 Z) j' a))) (pullU (𝟙 Z) _ (B.g (j a) (j' a))) ^ (n : ℤ)
  rw [e, zpow_natCast, map_pow, res_res]



theorem ev_res_pow {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ} {U W : Z.Opens} {y : CxPts q σ} (h : W ≤ U)
    (hy : y ∈ ptsIn q σ W) (u : Γ(Z, U)ˣ) (n : ℕ) :
    ev q σ W (res h u ^ n).val y = ev q σ U u.val y ^ (n : ℤ) := by
  rw [zpow_natCast, ← ev_res h hy, ev_eq hy, ev_eq hy, Units.val_pow_eq_pow_val, map_pow]
  rfl

end GlobalTheory.CuspDim.IsoPow
