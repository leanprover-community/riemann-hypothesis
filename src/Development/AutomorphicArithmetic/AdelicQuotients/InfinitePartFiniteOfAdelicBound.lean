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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem mapGL_id' {R : Type} [CommRing R] (n : ℕ) (x : Matrix.GeneralLinearGroup (Fin n) R) :
    PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.id R) x = x := by
  ext i j
  simp

theorem UpperTheory.infinitePart_finite_of_adelicBound :
    P2 → Triv → BoundE → InfF := by
  intro hP hT hB F _ _ n hn γ
  have hz : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have h1 : τ = 1 := by
      ext x
      exact τ.commutes x
    rw [h1]
    exact one_mem _
  obtain ⟨hg, hi, -⟩ := hT F
  have hi' : GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := F) = RingHom.id _ := hi
  have hB' := hB F F 1 hz n hn γ
  have hP' := (hP F F 1 hz n hn).2 γ γ
  rw [hg] at hB' hP'
  rw [hi'] at hP'
  simp only [mapGL_id'] at hB' hP'
  refine ⟨hB', fun hs D hD => ?_⟩
  have hN : PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (RingHom.id _)) (Module.finrank F F) γ = γ := by
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
    rfl
  obtain ⟨C, hC, h⟩ := hP' hs hN D hD
  exact ⟨C, hC, h⟩
