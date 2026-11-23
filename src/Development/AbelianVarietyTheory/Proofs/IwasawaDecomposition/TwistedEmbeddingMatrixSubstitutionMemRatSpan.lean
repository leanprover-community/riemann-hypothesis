module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.RatStab
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.Style
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

theorem twSub_eq_subP (D : D7) {n : ℕ} (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :
    twSub (embT D) M s P = C (∏ τ, (embT D τ (M : Matrix (Fin n) (Fin n) D.host.E).det) ^ (s τ)) *
      Formalism.L2.Forms.subP (fun τ => (M : Matrix (Fin n) (Fin n) D.host.E).map (embT D τ)) P := by
  rfl

theorem twSub_mem_ratSpan : ∀ (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) (M : GL (Fin n) D.host.E) (s : D.what₂.Tau → ℤ)
    (P0 : MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ),
    P0 ∈ Formalism.L2.Forms.RatSpan D lam → twSub (embT D) M s P0 ∈ Formalism.L2.Forms.RatSpan D lam := by
  classical
  intro D n lam M s P0 hP
  let A : Matrix (Fin n) (Fin n) D.host.E := (M : Matrix (Fin n) (Fin n) D.host.E)
  let ML : D.what₂.Tau → Matrix (Fin n) (Fin n) D.what₂.LL := fun τ => A.map (Formalism.L2.G.Cmp.tEL D τ)
  have hoM : ∀ τ, A.map (embT D τ) = (ML τ).map D.what₂.embLL := fun τ => by
    ext a b
    exact (Formalism.L2.G.Cmp.tEL_emb D τ _).symm
  have hdetA : A.det ≠ 0 := (Matrix.isUnits_det_units M).ne_zero
  have hMdet : ∀ τ, (ML τ).det ≠ 0 := by
    intro τ h
    apply hdetA
    have : Formalism.L2.G.Cmp.tEL D τ A.det = 0 := by
      rw [RingHom.map_det]; exact h
    exact (map_eq_zero _).1 this
  have hc : (∏ τ, (embT D τ A.det) ^ (s τ)) =
      D.what₂.embLL (∏ τ, (ML τ).det ^ s τ) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply, hoM τ, RingHom.map_det D.what₂.embLL, RingHom.mapMatrix_apply]
  rw [twSub_eq_subP]
  show C (∏ τ, (embT D τ A.det) ^ (s τ)) * Formalism.L2.Forms.subP (fun τ => A.map (embT D τ)) P0 ∈ _
  rw [hc, MvPolynomial.C_mul']
  induction hP using AddSubgroup.closure_induction with
  | mem p hp =>
    obtain ⟨r, f, hf, rfl⟩ := hp
    rw [map_smul, Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.substitution_tensor, smul_smul, ← map_mul]
    apply Formalism.L2.GlobalTheoryTheory.LemB.rat_ten D _ Finset.univ
    · intro τ _
      rw [hoM τ]
      exact Formalism.L2.GlobalTheoryTheory.LemB.rat_rowAct_mem D _ (Formalism.L2.DIV.natW_antitone _) (ML τ) (hMdet τ) _
        (Submodule.subset_span ⟨f τ, hf τ, rfl⟩)
    · intro τ hτ
      exact absurd (Finset.mem_univ τ) hτ
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.IntegralityCompare

end
