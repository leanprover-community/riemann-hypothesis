module

public import Formalism.LocalToGlobal.HermitianForms.TiedStep
public import Formalism.LocalToGlobal.HermitianForms.TiedBrRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Matrix

theorem exists_change {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (M M' : ι → Matrix (Fin n) (Fin n) ℂ) (hM : ∀ τ, IsUnit (M τ).det) (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : P ∈ CSpan lam) : ∃ Q ∈ CSpan lam, fnOf G s M' P = fnOf G s M Q := by
  refine ⟨_, ?_, fnOf_change G s M M' hM P⟩
  exact Submodule.smul_mem _ _ (blkRow_mem _ _ hP)

variable {D : D7} {u : D.what₂.Word}

theorem atInf_inv_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) (hA : IsUnit A.det) (τ : D.what₂.Tau) :
    IsUnit (atInf (embT D) A⁻¹ τ).det := by
  unfold atInf
  have h := (Matrix.isUnit_nonsing_inv_det A hA).map (embT D τ)
  first
  | (rw [RingHom.map_det, RingHom.mapMatrix_apply] at h; exact h)

variable (Tf : FormsTied D u)
  (B : D.what₂.places.Pl → (D.fm u).clsP → Matrix (Fin (D.R.N D.R.m - 1)) (Fin (D.R.N D.R.m - 1)) D.host.E)
  (hB : ∀ w c, IsUnit (B w c).det)

include hB


end Formalism.L2.Forms
