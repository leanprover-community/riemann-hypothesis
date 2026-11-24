module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.JacGL1


open GlobalTheory.SmGL GlobalTheory.PRep Matrix in
theorem jac_mulSingle_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin d) k) V) (ω : kˣ →* ℂˣ) (s' : ℕ) (b : Fin s' → ℕ) (f : (Σ j, Fin (b j)) ≃ Fin d) (j : Fin s'), d = 1 → b j = 1 → GlobalTheory.SmGL.HasCentralChar σ ω → ∀ (z : kˣ) (x : GlobalTheory.PRep.Jacquet σ (GlobalTheory.SmGL.unipRad k f)), GlobalTheory.SmGL.jac f σ (Pi.mulSingle j (Matrix.GeneralLinearGroup.scalar (Fin (b j)) z)) x = (ω z : ℂ) • x := by
  intro k _ _ _ _ d V _ _ σ ω s' b f j hd hj hω z x
  have hsum : ∑ i, b i = 1 := by
    have := Fintype.card_congr f
    simpa [Fintype.card_sigma, hd] using this
  have hsplit := Finset.add_sum_erase Finset.univ b (Finset.mem_univ j)
  have ha : ∀ i, i ≠ j → IsEmpty (Fin (b i)) := fun i hi => by
    have h0 : ∑ i ∈ Finset.univ.erase j, b i = 0 := by omega
    rw [Finset.sum_eq_zero_iff.1 h0 i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)]
    infer_instance
  have h1 : leviEmb k f (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) =
      GeneralLinearGroup.scalar (Fin d) z := by
    ext i i'
    obtain ⟨⟨a, y⟩, rfl⟩ := f.surjective i
    obtain ⟨⟨a', y'⟩, rfl⟩ := f.surjective i'
    obtain rfl : a = j := by_contra fun h => (ha a h).elim y
    obtain rfl : a' = a := by_contra fun h => (ha a' h).elim y'
    rw [leviEmb_apply_same]
    simp [GeneralLinearGroup.scalar, diagonal_apply]
  have h2 : modExp (fun i => Fin (b i)) j = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
    · intro a hb
      have := ha a (Finset.mem_filter.1 hb).2.ne'
      exact Nat.cast_eq_zero.2 Fintype.card_eq_zero
  have h3 : deltaHalf k (fun i => Fin (b i))
      (Pi.mulSingle j (GeneralLinearGroup.scalar (Fin (b j)) z)) = 1 := by
    rw [deltaHalf_apply]
    refine Finset.prod_eq_one fun a _ => ?_
    by_cases hb : a = j
    · subst hb
      simp [h2]
    · rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one]
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (jac_mk f σ _ v).trans ?_
  rw [h3, h1, hω z v, inv_one, Units.val_one, one_smul]
  exact map_smul (Submodule.mkQ _) _ _

end GlobalTheory.JacGL1
