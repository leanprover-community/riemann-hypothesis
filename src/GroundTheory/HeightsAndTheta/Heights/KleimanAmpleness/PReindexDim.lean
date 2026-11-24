module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltTer
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

theorem coneMap_rename {F : Type} [Field F] {κ : Type} {Ω : Type} [Field Ω] [Algebra F Ω] (x' : κ → Ω) {N : ℕ}
    (e : κ ≃ Fin (N + 1)) (p : NumbersDVR.MRing (fun _ : Unit => κ) F) :
    uniqueAlgEquiv Ω Unit (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p) =
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename (fun v : Σ _ : Unit, κ => e v.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMapOver, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]

theorem ReindexDim.proof : ReindexDim.Statement := by
  intro F _ κ _ Ω _ _ x' N e
  let σ : (Σ _ : Unit, κ) ≃ Fin (N + 1) :=
    { toFun := fun v => e v.2, invFun := fun i => ⟨(), e.symm i⟩, left_inv := fun _ => by simp,
      right_inv := fun _ => by simp }
  let f : NumbersDVR.MRing (fun _ : Unit => κ) F ≃+* Kleiman.Poly F N := (renameEquiv F σ).toRingEquiv
  have hc : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') =
      (Kleiman.primeOf (S := F) (x' ∘ e.symm)).comap f.toRingHom := by
    ext p
    change mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') p = 0 ↔
      ReciprocityTheory.ChartRestriction.G.Geo.coneMap F (x' ∘ e.symm) (rename σ p) = 0
    rw [← (uniqueAlgEquiv Ω Unit).injective.eq_iff, map_zero]
    exact Iff.of_eq (congrArg (· = 0) (coneMap_rename x' e p))
  have h : Kleiman.primeOf (S := F) (x' ∘ e.symm) = (mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x')).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
