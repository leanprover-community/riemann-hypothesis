module

public import Development.EtaleCohomology.EtaleSheaves.AugBijPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC GlobalTheory.EtC.PrimLoc

theorem UpperTheory.Cb.augmentation_map_bijective :
    LateralTheory.E.AugBijPf.Root := by
  intro q U hq
  rcases subsingleton_or_nontrivial Γ(U, ⊤) with hA | hA
  · exact ⟨U, 𝟙 U, inferInstance, fun u => ⟨u, rfl⟩, ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩⟩
  have hq0 : NeZero q := ⟨by rintro rfl; simp at hq⟩
  let B := AdjoinRoot (cyclotomic q Γ(U, ⊤))
  let φ : CommRingCat.of Γ(U, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap _ B)
  have he : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr (cyc_etale q hq))
  have hs : Surjective (Spec.map φ) :=
    ⟨adjoinRoot_surj _ (cyclotomic.monic q _)
      (by simp [natDegree_cyclotomic, Nat.totient_pos, Nat.pos_of_ne_zero hq0.out, hq0.out])⟩
  refine ⟨pullback U.toSpecΓ (Spec.map φ), pullback.fst _ _, inferInstance, ?_, ?_⟩
  · intro u
    exact (Surjective.surj (f := pullback.fst U.toSpecΓ (Spec.map φ))) u
  · exact ⟨Prim.map ((pullback.snd U.toSpecΓ (Spec.map φ)).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) (cyc_root q hq)⟩
