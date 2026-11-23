module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCoverStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isReg_of_locally : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (k : (Fin g → ℂ) → ℂ), (∀ z ∈ pre u.ex U, ∃ W : A.left.Opens, W ≤ U ∧ z ∈ pre u.ex W ∧ IsReg u.ex W k) → IsReg u.ex U k := by
  intro A _ g L u hA U k h
  choose! W hWU hzW hreg using h
  let K : Type := {z // z ∈ pre u.ex U}
  let V : K → A.left.Opens := fun z => W z.1
  have hVU : ∀ i : K, V i ≤ U := fun i => hWU i.1 i.2
  have hb : ∀ i : K, ∃ b : Γ(A.left, V i), ∀ z ∈ pre u.ex (V i), k z = val u.ex (V i) b z := fun i => hreg i.1 i.2
  choose b hb using hb
  have hcov : U ≤ ⨆ i, V i := GlobalTheory.T.le_iSup_of_uniformisationParameters_cover A g L u hA U K V fun z hz => ⟨⟨z, hz⟩, hzW z hz⟩
  have hcompat : TopCat.Presheaf.IsCompatible A.left.sheaf.1 V b := by
    intro i j
    rw [← sub_eq_zero]
    refine GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA (V i ⊓ V j) _ fun z hz => ?_
    have hz' := (GlobalTheory.top_le_preimage_inf (u.ex z).left (V i) (V j)).1 hz
    have e1 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLELeft (V i) (V j)).op (b i) hz
    have e2 := GlobalTheory.valAt'_map (u.ex z).left (TopologicalSpace.Opens.infLERight (V i) (V j)).op (b j) hz
    refine (GlobalTheory.valAt'_sub (u.ex z).left (V i ⊓ V j) _ _).trans ?_
    rw [sub_eq_zero]
    exact e1.trans (((hb i z hz'.1).symm.trans (hb j z hz'.2)).trans e2.symm)
  obtain ⟨s, hs, -⟩ := A.left.sheaf.existsUnique_gluing' V U (fun i => homOfLE (hVU i)) hcov b hcompat
  refine ⟨s, fun z hz => ?_⟩
  have h1 := hb ⟨z, hz⟩ z (hzW z hz)
  have h2 := GlobalTheory.valAt'_map (u.ex z).left (homOfLE (hVU ⟨z, hz⟩)).op s (hzW z hz)
  rw [h1, ← hs ⟨z, hz⟩]
  exact h2

end GlobalTheory.CechPer
