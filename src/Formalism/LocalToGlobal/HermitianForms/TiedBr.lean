module

public import Formalism.LocalToGlobal.HermitianForms.LastCoordinateUniformizerVectorSpansOrthogonalLi
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
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts NumberField

variable {D : D7}

def bZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  fun a b => if hb : (b : ℕ) < D.R.N D.R.m - 1 then iXm D a ⟨b, hb⟩ else z0 a / ((D.mem u).A.T : D.host.E)

def mZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ :=
  atInf (embT D) (bZ u z0)⁻¹

theorem mZ_isUnit {u : D.what₂.Word} {z0 : Fin (D.R.N D.R.m) → D.host.E} (hB : IsUnit (bZ u z0).det) (τ : D.what₂.Tau) :
    IsUnit (mZ u z0 τ).det := by
  have h1 : IsUnit ((bZ u z0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hB
  have h2 : IsUnit ((embT D τ).mapMatrix (bZ u z0)⁻¹).det := by
    rw [← RingHom.map_det]
    exact h1.map _
  exact h2

end Formalism.L2.Forms
