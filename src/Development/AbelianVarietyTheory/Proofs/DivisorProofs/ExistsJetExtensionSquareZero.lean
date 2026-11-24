module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomJet
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

set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_jet_factor {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {k : K.K} {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (hd : f₁.deg = f₂.deg)
    (hJ : ∀ a, n a ∈ T.J) (hn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) :
    ∃ χ : K.jet k ⟶ T, χ.deg = f₁.deg ∧ jet0 k ≫ χ = f₁ ∧ jet1 k ≫ χ = f₂ ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        χ.φ x = f₁.φ (x.fst : Hol (K.W k)) + ∑ a, f₁.φ (x.snd a : Hol (K.W k)) * n a := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet
  | (apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareLiftLemmas.exists_hom_jet ..)

end GlobalTheory.AnPer.Charts
