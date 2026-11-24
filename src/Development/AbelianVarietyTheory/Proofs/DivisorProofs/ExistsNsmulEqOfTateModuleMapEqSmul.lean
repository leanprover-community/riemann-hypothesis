module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfKillsTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TlLevSurjKer
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

theorem exists_nsmul_eq_of_tmap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B),
      tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  intro K _ l _ hl A B f φ hf
  refine exists_nsmul_eq_of_kills_torsion K A B f l hl fun x hx => ?_
  obtain ⟨t, ht⟩ := (tl_lev_surj_ker K l A 1).1 x (by rwa [pow_one])
  have h1 : (tmap l A B f t).lev 1 = x ≫ f.hom := by rw [lev_tmap, ht]
  rw [← h1, hf, LinearMap.smul_apply]
  exact ((tl_lev_surj_ker K l B 1).2 _).2 ⟨φ t, by rw [pow_one]⟩

end GlobalTheory.AV.AbVar
