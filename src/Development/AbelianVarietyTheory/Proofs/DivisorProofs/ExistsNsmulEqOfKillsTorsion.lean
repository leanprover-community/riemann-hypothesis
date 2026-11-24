module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfKillsGeometricTorsionPointsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernelStatement
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem comp_id_pow_eq {K : Type} [Field K] (A : AbVar K) {T : Over (Sp K)} (x : T ⟶ A.X) (n : ℕ) :
    x ≫ (𝟙 A.X) ^ n = x ^ n := by
  induction n with
  | zero => simp [pow_zero, MonObj.comp_one]
  | succ k ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

theorem exists_nsmul_eq_of_kills_torsion : ∀ (K : Type) [Field K] (A C : AbVar K) (f : A ⟶ C) (n : ℕ),
    (n : K) ≠ 0 → (∀ x : A.Pt, x ^ n = 1 → x ≫ f.hom = 1) → ∃ g : A ⟶ C, f = n • g := by
  intro K _ A C f n hn hf
  have hn0 : (n : ℤ) ≠ 0 := by
    intro h
    apply hn
    have : n = 0 := by exact_mod_cast h
    simp [this]
  obtain ⟨hiso, -⟩ := GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A (n : ℤ) hn0
  have hiso' : IsIsogeny (n • 𝟙 A) := by rwa [natCast_zsmul] at hiso
  have hkill := GlobalTheory.T.comp_eq_one_of_kills_geometric_torsionPoints K A C f n hn hf
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel K A A C (n • 𝟙 A) f hiso' (fun T x hx => by
    apply hkill T x
    rw [nsmul_hom, id_hom, comp_id_pow_eq] at hx
    exact hx)
  refine ⟨g, ?_⟩
  rw [← hg, Preadditive.nsmul_comp, Category.id_comp]

end GlobalTheory.AV.AbVar
