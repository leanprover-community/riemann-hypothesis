module

public import Formalism.LocalRingCardinality.DataTheta
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
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.SharpRestriction.FamCore
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ZetaProductPairs

open Formalism.BasicNotions

structure Loc (D : D7) (T : ThetaX D) where

  gl1 : D.what₂.Word → T.Gf (D.sp.Y 0)

  glSym : D.what₂.Word → T.Gf (D.sp.Y 0)

  ArchDat : D.what₂.Word → Type
  ArchDat_ne : ∀ u, Nonempty (ArchDat u)

  ellT : ∀ u, ArchDat u → ℂ

  Au : ∀ u, ArchDat u → ℂ

  B0 : ∀ u, D.what₂.Mu u →ₗ[ℂ] D.what₂.EE →ₗ[ℂ] ℂ

  zeX : D.what₂.Word → D.what₂.Tup → ℂ

  zeta_at_base_tuple : ∀ u, zeX u D.what₂.mu0 = 1

  zeX_fin : ∀ u μ, ∃ n : ℕ, 0 < n ∧ zeX u μ ^ n = 1

variable {D : D7}

variable {T : ThetaX D}

section Local

open MeasureTheory Matrix ComplexConjugate Finset

def qE (q : ℝ) (a c : ℕ) : ℝ := ∏ i ∈ Icc a c, (1 - q ^ (-(i : ℤ)))

def zetaProd (q : ℝ) (n : ℕ) : ℝ := (qE q 1 n)⁻¹

def idxPar (q : ℝ) (r s : ℕ) : ℝ := TH.parIdx q r s

def Lpair (q : ℝ) (t : ℕ) (x : ℂ) : ℂ :=
  (∏ s ∈ Icc 1 t, ((1 - x * ((q : ℂ) ^ (-(s : ℤ)))) * (1 - x⁻¹ * ((q : ℂ) ^ (-(s : ℤ))))))⁻¹


end Local

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (A : TH.ProvA)
  (GF : ∀ x (i : Fm.Ix x), Formalism.MainNotions.product_first_zeroth_parts.Th22 (Fm.D x i))
  (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.ex x hx i).th)

end Family

end Formalism.MainNotions.ZetaProductPairs

end
