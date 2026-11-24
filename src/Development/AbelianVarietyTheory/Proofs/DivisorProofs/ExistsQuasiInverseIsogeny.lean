module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteHomKernelKilledByNatStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSurjectiveGeomFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
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
import Mathlib.Tactic.Basify
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

theorem exists_quasiInverse_isogeny : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), IsIsogeny f →
    ∃ (n : ℕ) (g : B ⟶ A), 0 < n ∧ IsIsogeny g ∧ f ≫ g = n • 𝟙 A ∧ g ≫ f = n • 𝟙 B := by
  intro K _ A B f hf
  obtain ⟨hdim, -, -, -⟩ := GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hf
  obtain ⟨n, hn, hker⟩ := GlobalTheory.T.abelianVariety_finiteHom_kernel_killed_by_nat K A B f hf.1
  have hB := B.smooth
  have hA := A.smooth
  rw [hdim] at hA
  obtain ⟨h, hh, hfh, hhf⟩ := GlobalTheory.IsogenyQuasiInverse.exists_quasiInverse K A.X B.X B.dim A.ab B.ab hA hB
    f.hom inferInstance n hn hker
  let g : B ⟶ A := Hom.mk (A := B) (B := A) h (h := hh)
  have e1 : f ≫ g = n • 𝟙 A := by
    apply Subtype.ext
    change (f ≫ g).hom = (n • 𝟙 A).hom
    simp [g, hfh]
  have e2 : g ≫ f = n • 𝟙 B := by
    apply Subtype.ext
    change (g ≫ f).hom = (n • 𝟙 B).hom
    simp [g, hhf]
  refine ⟨n, g, hn, ?_, e1, e2⟩
  have hm : IsIsogeny ((n : ℤ) • 𝟙 B) := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K B n (by exact_mod_cast hn.ne')).1
  rw [natCast_zsmul, ← e2] at hm
  exact (((GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K B A B g f hdim.symm hdim).1).mp hm).1

end GlobalTheory.AV.AbVar
