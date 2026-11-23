module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SelmerRankBoundLaurent
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal

theorem UpperTheory.maximalCompactNorm_of_unit_criterion :
    K1 → Triv → UnitIff → Compat → SelmerRankBoundLaurent := by
  intro hK hT hU hC F _ _ n hn γ hγ
  have hincl : PositivityTheory.Rg.Tf.Loc.incl γ = γ := by
    ext i j
    rfl
  have hnorm : PositivityTheory.Rg.Tf.Loc.normGL (1 : F ≃ₐ[F] F) γ = PositivityTheory.Rg.Tf.Loc.incl γ := by
    rw [hincl, PositivityTheory.Rg.Tf.Loc.normGL, Module.finrank_self]
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
  have h1 : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  obtain ⟨-, -, -, c4, -, -, -, c8⟩ := hC F F 1 n
  filter_upwards [hK F F 1 h1 n hn γ γ hγ hnorm] with v hv x
  have hdiag : mapGL n (atFin v) (AdelicGLn.diagonal F n γ) =
      mapGL n (incFin F v) (finAt v (AdelicGLn.diagonal F n γ)) := by
    have h := c4 v (AdelicGLn.diagonal F n γ)
    rw [c8, hincl] at h
    exact h
  have hgal : ∀ y : GL (Fin n) (CompletionsOver F v), mapGL n (galFin (1 : F ≃ₐ[F] F) v) y = y := fun y => by
    rw [((hT F).2.2 v).1]
    ext i j
    rfl
  have key := hv (mapGL n (incFin F v) x)
  rw [hdiag, hgal, ← map_inv, ← map_mul, ← map_mul, hU F F n v] at key
  rw [key]
  constructor
  · rintro ⟨t, ht, y, hy, e⟩
    refine ⟨t, ht, t⁻¹ * x, ?_, by group⟩
    rw [← hU F F n v, map_mul, map_inv, e, inv_mul_cancel_left]
    exact hy
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht, mapGL n (incFin F v) y, (hU F F n v y).2 hy, map_mul _ _ _⟩
