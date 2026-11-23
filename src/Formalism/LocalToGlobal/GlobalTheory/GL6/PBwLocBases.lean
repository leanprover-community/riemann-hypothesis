module

public import Formalism.LocalToGlobal.HermitianForms.TiedStep
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB NumberField Classical

variable (D : D7) (u : D.what₂.Word)

theorem bwB_clsCrd_lat (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule.IsLattice D.host.E (clsCrd D u i hi c) := by
  unfold clsCrd
  exact Submodule.IsLattice.of_fg D.host.E ((D.clsLat_lat u i c).fg.map _)

theorem bwB_gramN_det (i : ℕ) (hi : i ≤ D.R.m) : IsUnit (gramN D i hi).det := by
  letI := D.host.cmStar
  unfold gramN
  rw [Matrix.det_reindex_self, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfa : ∀ a, (D.sp.X i).hT ((D.sp.X i).frame a) (∑ b, v b • (D.sp.X i).frame b) = 0 := by
    intro a
    have h := congrFun hv a
    have e : Matrix.mulVec (D.sp.X i).gram v a =
        ∑ b, (D.sp.X i).hT ((D.sp.X i).frame a) ((D.sp.X i).frame b) * v b := rfl
    rw [e] at h

    simp only [map_sum, map_smul, smul_eq_mul]
    simpa [mul_comm] using h
  have hy : ∀ x, (D.sp.X i).hT x (∑ b, v b • (D.sp.X i).frame b) = 0 := by
    intro x
    have h0 : (D.sp.X i).hT.flip (∑ b, v b • (D.sp.X i).frame b) = 0 :=
      (D.sp.X i).frame.ext (fun a => by simpa using hfa a)
    simpa using congrArg (fun f => f x) h0
  have hy0 := (D.sp.X i).nondeg.2 _ hy
  have hz := Fintype.linearIndependent_iff.mp (D.sp.X i).frame.linearIndependent v hy0
  exact hv0 (funext hz)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
