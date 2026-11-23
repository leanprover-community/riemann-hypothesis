module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleForms
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagBundleSectionDiv
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PIntNumSymm
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleCutProof

theorem intNumL_cons_eq_snoc {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type} [Field F] (P : Ideal (MRing ι F)) (x : K → ℤ)
    (L : List (K → ℤ)) :
    intNumL F P (x :: L) = intNum F P (Fin.snoc (α := fun _ => K → ℤ) L.get x) := by
  have hget : (x :: L).get = Fin.cons (α := fun _ => K → ℤ) x L.get := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  have h := FieldNumbers.IntNumSymm.proof F K ι P (L.length + 1)
    (Fin.cons (α := fun _ => K → ℤ) x L.get) (finRotate _)
  rw [intNumL, hget, Fin.snoc_eq_cons_rotate, ← h]
  rfl

theorem cycEval_single {K : Type} {ι : K → Type} {F : Type} [Field F]
    (n : Ideal (MRing ι F) → ℤ) (Z : Ideal (MRing ι F)) :
    cycEval n (fun W => by classical exact if W = Z then 1 else 0) = n Z := by
  classical
  unfold cycEval
  rw [finsum_eq_single _ Z (fun W hW => by simp [hW])]
  simp

end FlagBundleCutProof


open FlagBundleCutProof in
theorem FlagBundleCut.proof (hDim : FlagBundleDim.Statement)
    (hForms : FlagBundleSectionForms.Statement) (hDiv : FlagBundleSectionDiv.Statement)
    (hCut : FieldNumbers.CutRational.Statement.{0}) : FlagBundleCut.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi L hL
  obtain ⟨bf, bg, f, g, hf, hg, hdeg, hfP, hgP, hval⟩ :=
    hForms F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i
  have hdiv := hDiv F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi bf bg f g hf hg hdeg hgP hval
  obtain ⟨hP, hrel⟩ :=
    hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) =
      ((L.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hrel]
    congr 2
    omega
  have h := hCut F (Option K) (bundleIdx ι M) _ hP L.length hrel' bf bg f g hf hg hfP hgP L.get
  rw [intNumL_cons_eq_snoc, ← hdeg, h, funext hdiv, intNumL]
  classical
  convert cycEval_single (fun W => intNum F W L.get) (projIdeal F y w φ (truncCoord t i))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
