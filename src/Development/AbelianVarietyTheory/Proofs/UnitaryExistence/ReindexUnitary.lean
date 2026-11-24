module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InfAdeleTensorBijective
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

namespace GlobalTheory.MarkUnit

theorem infMat_unitary {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x)) (θ : Ainf F ⊗[F] E →+* ℂ) (hθ : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ)
    (h : HA (AF F) σ J) :
    ((Formalism.MainNotions.StandardLattice.infMat σ J θ h).map (starRingEnd ℂ)).transpose * J.map τ * Formalism.MainNotions.StandardLattice.infMat σ J θ h =
      J.map τ := by
  let φ : AF F ⊗[F] E →+* ℂ :=
    θ.comp (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hφ : ∀ (a : AF F) (x : E), φ (a ⊗ₜ x) =
      GlobalTheory.InfAdeleCM.ext (τ.comp (algebraMap F E)) (fstA F a) * τ x := fun a x =>
    GlobalTheory.InfAdeleCM.hom_tmul τ θ hθ.1 hθ.2 (fstA F a) x
  have h1 : ∀ z, φ (sigR (AF F) σ z) = starRingEnd ℂ (φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      have : sigR (AF F) σ (a ⊗ₜ x) = a ⊗ₜ σ x := rfl
      rw [this, hφ, hφ, map_mul, GlobalTheory.InfAdeleCM.conj_ext, hτ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h2 : ∀ x, φ (inclR (AF F) x) = τ x := by
    intro x
    have : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ x := rfl
    rw [this, hφ, map_one, map_one, one_mul]
  have hu : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1 * JR (AF F) J * (HA.mat (AF F) σ J h).1 =
      JR (AF F) J := (show HR (AF F) σ J from h).2
  have hm : Formalism.MainNotions.StandardLattice.infMat σ J θ h = (HA.mat (AF F) σ J h).1.map φ := rfl
  have hJ : (JR (AF F) J).map φ = J.map τ := by
    ext a b
    exact h2 _
  have hc : (Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J h).1).map φ =
      (((HA.mat (AF F) σ J h).1.map φ).map (starRingEnd ℂ)).transpose := by
    ext a b
    exact h1 _
  have := congrArg (fun m => Matrix.map m φ) hu
  simp only [Matrix.map_mul] at this
  rw [hJ, hc] at this
  rw [hm]
  exact this


end GlobalTheory.MarkUnit
