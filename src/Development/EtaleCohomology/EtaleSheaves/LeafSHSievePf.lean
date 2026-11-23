module

public import Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSievePf

theorem LeafSHSieve_of : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := by
  intro X _ hSH S hS
  obtain ⟨hHens, hSep⟩ := hSH
  let A : Type := Γ(X, ⊤)
  let K : Type := IsLocalRing.ResidueField A
  let π : A →+* K := IsLocalRing.residue A
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  let x : Spec (.of K) ⟶ X := Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber K).jointly_surjective _
    (Scheme.Cover.mem_grothendieckTopology 𝒰) x
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
  have hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv := by
    exact (Category.assoc _ _ _).trans hy
  obtain ⟨l, ⟨-, hl⟩, -⟩ := GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π
    IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'
  have hmem : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have := S.downward_closed hmem (X.isoSpec.hom ≫ l)
  have e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X := by rw [Category.assoc, hl, Iso.hom_inv_id]
  rwa [e] at this

end LateralTheory.E.LeafSHSievePf
